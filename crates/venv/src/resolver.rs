// Copyright 2026 Pex project contributors.
// SPDX-License-Identifier: Apache-2.0

use std::borrow::Cow;
use std::ffi::OsStr;
use std::io;
use std::io::{BufRead, BufReader, Read, Seek, SeekFrom, Write};
use std::ops::Range;
use std::path::{Component, Path, PathBuf};
use std::sync::LazyLock;

use anyhow::{anyhow, bail};
use fs_err as fs;
use fs_err::File;
use pelite::image::IMAGE_SUBSYSTEM_WINDOWS_GUI;
use pelite::{PeFile, Wrap};
use platform::{PosixPath, is_executable};
use python_platform::PythonVersion;
use regex::Regex;
use wheel::{EntryPoints, MetadataDirs, Record, parse_root_is_purelib_from_wheel};
use zip::ZipArchive;

use crate::Virtualenv;

struct InstallPaths<'a> {
    python_version: PythonVersion,
    data: Cow<'a, Path>,
    headers_base: Cow<'a, Path>,
    platlib: Cow<'a, Path>,
    purelib: Cow<'a, Path>,
    scripts: Cow<'a, Path>,
}

impl<'a> InstallPaths<'a> {
    fn for_venv(venv: &'a Virtualenv<'a>) -> anyhow::Result<Self> {
        let get_sysconfig_path = |name| {
            venv.interpreter
                .details
                .paths
                .get(name)
                .map(PathBuf::as_path)
                .map(Cow::Borrowed)
                .ok_or_else(|| {
                    anyhow!(
                        "The venv at {venv} unexpectedly has no sysconfig path for '{name}'",
                        venv = venv.prefix().display()
                    )
                })
        };

        Ok(Self {
            python_version: venv.interpreter.details.version,
            data: get_sysconfig_path("data")?,
            headers_base: Cow::Owned(venv.prefix().join("include").join("site").join(format!(
                "python{major}.{minor}",
                major = venv.interpreter.details.version.major,
                minor = venv.interpreter.details.version.minor
            ))),
            platlib: get_sysconfig_path("platlib")?,
            purelib: get_sysconfig_path("purelib")?,
            scripts: get_sysconfig_path("scripts")?,
        })
    }

    fn headers(&self, project_name: &str) -> PathBuf {
        self.headers_base.join(project_name)
    }
}

struct InstalledWheel {
    project_name: String,
    version: String,
    record: Record,
    metadata_dirs: MetadataDirs,
    root_is_purelib: bool,
    entry_points: EntryPoints,
}

impl InstalledWheel {
    fn load(dist_info_dir: PathBuf) -> anyhow::Result<Self> {
        let metadata_dirs = MetadataDirs::from_dist_info_dir(&dist_info_dir)?;
        let installed_wheel_dir = dist_info_dir.parent().ok_or_else(|| anyhow!("XXX"))?;
        let (record, _) = Record::parse(installed_wheel_dir, &metadata_dirs)?;
        let root_is_purelib =
            parse_root_is_purelib_from_wheel(fs::read(dist_info_dir.join("WHEEL"))?.as_slice())?;
        let entry_points = {
            let entry_points_txt = dist_info_dir.join("entry_points.txt");
            if entry_points_txt.exists() {
                EntryPoints::load(File::open(entry_points_txt)?)?
            } else {
                EntryPoints::empty()
            }
        };
        Ok(Self {
            project_name: metadata_dirs.borrow_project_name().to_string(),
            version: metadata_dirs.borrow_version().to_string(),
            record,
            metadata_dirs,
            root_is_purelib,
            entry_points,
        })
    }

    // https://docs.python.org/2.7/library/sysconfig.html#sysconfig.get_path
    // Each scheme is itself composed of a series of paths and each path has a unique identifier. Python currently uses eight paths:
    //
    //     stdlib: directory containing the standard Python library files that are not platform-specific.
    //     platstdlib: directory containing the standard Python library files that are platform-specific.
    //
    //     platlib: directory for site-specific, platform-specific files.
    //     purelib: directory for site-specific, non-platform-specific files.
    //
    //     include: directory for non-platform-specific header files.
    //     platinclude: directory for platform-specific header files.
    //
    //     scripts: directory for script files.
    //     data: directory for data files.
    //
    // {distribution}-{version}.data/ contains one subdirectory for each non-empty install scheme
    // key not already covered, where the subdirectory name is an index into a dictionary of install
    // paths (e.g. data, scripts, headers, purelib, platlib).
    //
    // Of these 5 headers DNE. You'd think sysconfig_paths["include"] (or "platinclude") would be
    // the right answer here but both `pip`, and by emulation, `uv pip`, map `*.data/headers` to
    // `<venv>/include/site/pythonX.Y/<project name>`. Traditional PEXes honors this; so we need to
    // as well.
    //
    // The "mess" is admitted and described at length here:
    // + https://discuss.python.org/t/clarification-on-a-wheels-header-data/9305
    // + https://discuss.python.org/t/deprecating-the-headers-wheel-data-key/23712

    const COMPILED_PYTHON_EXTENSIONS: &[&str] = &["pyc", "pyo", "pyd"];
    const IGNORED_METADATA_FILES: &[&str] = &["RECORD", "INSTALLER", "REQUESTED"];

    fn pack(&self, install_paths: &InstallPaths, _dest: impl Write + Seek) -> anyhow::Result<()> {
        // read the RECORD and for each installed file
        // 1. Ignore `*.py{cod}`, `RECORD`, `INSTALLER`, `REQUESTED` if in RECORD.
        // 2. If path is bin/X (or Scripts\X) and file_stem matches entry_points.txt entry, ignore
        //    it.
        // 3. If path is a .data/X spread, un-spread to that .data/X
        //   + For .data/scripts files with venv python shebang or -> #!pythonw?
        //   + For .data/scripts files with venv /bin/sh re-director shebang -> #!pythonw?
        // 4. Otherwise; for X pack at X
        // 5. Finalize RECORD
        let site_packages_dir = if self.root_is_purelib {
            &install_paths.purelib
        } else {
            &install_paths.platlib
        };
        for entry in self.record.entries() {
            if self.metadata_dirs.dist_info_dir().contains(&entry.path)
                && entry.path.components().count() == 2
                && let Some(file_name) = entry.path.file_name().and_then(OsStr::to_str)
                && Self::IGNORED_METADATA_FILES.contains(&file_name)
            {
                continue;
            }
            if let Some(ext) = entry.path.extension().and_then(OsStr::to_str)
                && Self::COMPILED_PYTHON_EXTENSIONS.contains(&ext)
            {
                continue;
            }

            // TODO: XXX: Re-write python shebang (including /bin/sh re-directors) as #!pythonw?
            let mut needs_script_rewrite: Option<PythonScript> = None;
            let dst_path = if entry.path.is_relative()
                && entry
                    .path
                    .components()
                    .all(|component| matches!(component, Component::CurDir | Component::Normal(_)))
            {
                PosixPath::new(entry.path.clone(), false)?
            } else {
                let abs_path = if entry.path.is_relative() {
                    site_packages_dir.join(&entry.path).canonicalize()?
                } else {
                    entry.path.canonicalize()?
                };
                let data_dir = self.metadata_dirs.data_dir().as_path();
                let data_dir_rel_path = if let Ok(scripts_rel_path) =
                    abs_path.strip_prefix(&install_paths.scripts)
                {
                    let has_parent = scripts_rel_path
                        .parent()
                        .map(|parent| !parent.is_empty())
                        .unwrap_or_default();
                    if !has_parent
                        && let Some(script_name) =
                            scripts_rel_path.file_stem().and_then(OsStr::to_str)
                        && self.entry_points.is_script(script_name)
                    {
                        continue;
                    }
                    needs_script_rewrite =
                        PythonScript::detect(&abs_path, install_paths.python_version)?;
                    data_dir.join("scripts").join(scripts_rel_path)
                } else if let Ok(headers_rel_path) =
                    abs_path.strip_prefix(install_paths.headers(&self.project_name))
                {
                    data_dir.join("headers").join(headers_rel_path)
                } else if let Ok(platlib_rel_path) = abs_path.strip_prefix(&install_paths.platlib) {
                    data_dir.join("platlib").join(platlib_rel_path)
                } else if let Ok(purelib_rel_path) = abs_path.strip_prefix(&install_paths.purelib) {
                    data_dir.join("purelib").join(purelib_rel_path)
                } else if let Ok(data_rel_path) = abs_path.strip_prefix(&install_paths.data) {
                    data_dir.join("data").join(data_rel_path)
                } else {
                    bail!("XXX: Unexpected path: {path}", path=entry.path.display())
                };
                PosixPath::new(Cow::Owned(data_dir_rel_path), false)?
            };
            if let Some(python_script) = needs_script_rewrite {
                let mut re_written = Vec::new();
                python_script.re_write(&mut re_written)?;
                eprintln!(
                    "||| re-write from:\n{original}\n||| to:\n{re_written}",
                    original = match python_script {
                        PythonScript::Posix { path, .. } => {
                            fs::read_to_string(&path)?
                        }
                        PythonScript::Windows { path, .. } => {
                            path.display().to_string()
                        }
                    },
                    re_written = String::from_utf8(re_written)?
                )
            } else {
                eprintln!(
                    ">>> {src} -> {dst}",
                    src = entry.path.display(),
                    dst = dst_path
                )
            }
        }
        // TODO: XXX
        Ok(())
    }
}

fn collect_installed_wheels(venv: &Virtualenv) -> anyhow::Result<Vec<InstalledWheel>> {
    let mut installed_wheels = Vec::new();
    for entry in venv.prefix().join(&venv.site_packages_relpath).read_dir()? {
        if let Ok(entry) = entry
            && let Ok(file_type) = entry.file_type()
            && file_type.is_dir()
            && entry
                .file_name()
                .as_encoded_bytes()
                .ends_with(b".dist-info")
        {
            installed_wheels.push(InstalledWheel::load(entry.path())?);
        }
    }
    Ok(installed_wheels)
}

#[cfg_attr(test, derive(Debug, Eq, PartialEq))]
enum PythonScript {
    Posix {
        path: PathBuf,
        shebang_end: usize,
        is_windowed: bool,
        extra_shebang_content: Option<Range<usize>>,
    },
    Windows {
        path: PathBuf,
        is_windowed: bool,
    },
}

// See: https://peps.python.org/pep-0263/
static PEP_263_CODING_LINE_RE: LazyLock<Regex> = LazyLock::new(|| {
    Regex::new(r"^[ \t\f]*#.*?coding[:=][ \t]*([-_.a-zA-Z0-9]+)")
        .expect("This is a known good regex.")
});
static PIP_AND_UV_BIN_SH_RE_DIRECTOR_RE: LazyLock<Regex> = LazyLock::new(|| {
    Regex::new(r"^'''exec' .*(python|pypy).*").expect("This is a known good regex.")
});

impl PythonScript {
    fn detect(path: &Path, python_version: PythonVersion) -> anyhow::Result<Option<Self>> {
        if let Some(python_script) = Self::detect_posix(path, python_version)? {
            Ok(Some(python_script))
        } else {
            Self::detect_windows(path)
        }
    }

    fn detect_posix(path: &Path, python_version: PythonVersion) -> anyhow::Result<Option<Self>> {
        let mut buf_read = BufReader::new(File::open(path)?);
        let mut magic_buf: [u8; 2] = [0; 2];
        buf_read.read_exact(&mut magic_buf)?;
        if &magic_buf != b"#!" {
            return Ok(None);
        }
        let mut shebang = Vec::new();
        buf_read.read_until(b'\n', &mut shebang)?;
        shebang.make_ascii_lowercase();
        let interpreter =
            if let Some((interpreter, _)) = shebang.split_once(|x| x.is_ascii_whitespace()) {
                interpreter
            } else {
                shebang.as_slice()
            };
        let shebang_end = 2 /* #! */ + interpreter.len();

        let mut extra_shebang_content: Option<Range<usize>> = None;
        let mut is_windowed = false;
        let mut is_python = interpreter == b"python";
        if !is_python {
            is_windowed = interpreter == b"pythonw";
            is_python = is_windowed;
        }
        if !is_python && interpreter == b"/bin/sh" {
            let mut line_buffer = String::new();
            let mut start = shebang_end;
            let mut amount_read = buf_read.read_line(&mut line_buffer)?;
            if PEP_263_CODING_LINE_RE.is_match(&line_buffer) {
                start += amount_read;
                line_buffer.clear();
                amount_read = buf_read.read_line(&mut line_buffer)?;
            }
            if line_buffer != "'''': pshprs\n"
                && !PIP_AND_UV_BIN_SH_RE_DIRECTOR_RE.is_match(&line_buffer)
            {
                return Ok(None);
            }
            is_python = true;
            let mut end = start + amount_read;
            loop {
                line_buffer.clear();
                end += buf_read.read_line(&mut line_buffer)?;
                if line_buffer == "'''\n" {
                    break;
                }
            }
            extra_shebang_content = Some(start..end);
        }
        if !is_python {
            is_python = interpreter.ends_with(b"/python") || interpreter.ends_with(b"pypy");
        }
        if !is_python {
            is_python = interpreter
                .ends_with(format!("/python{major}", major = python_version.major).as_bytes())
                || interpreter
                    .ends_with(format!("/pypy{major}", major = python_version.major).as_bytes());
        }
        if !is_python {
            is_python = interpreter.ends_with(
                format!(
                    "/python{major}.{minor}",
                    major = python_version.major,
                    minor = python_version.minor
                )
                .as_bytes(),
            ) || interpreter.ends_with(
                format!(
                    "/pypy{major}.{minor}",
                    major = python_version.major,
                    minor = python_version.minor
                )
                .as_bytes(),
            );
        }

        if !is_python {
            Ok(None)
        } else {
            Ok(Some(Self::Posix {
                path: buf_read.into_inner().into_path(),
                shebang_end,
                is_windowed,
                extra_shebang_content,
            }))
        }
    }

    fn detect_windows(path: &Path) -> anyhow::Result<Option<Self>> {
        if !is_executable(path)? {
            return Ok(None);
        }
        if let Ok(mut zip) = ZipArchive::new(File::open(path)?)
            && zip.by_name("__main__.py").is_ok()
        {
            let zip_offset = zip.offset();
            let file = zip.into_inner();
            let pe_contents_len = file.metadata()?.len() - zip_offset;
            let mut contents = Vec::with_capacity(pe_contents_len as usize);
            let mut pe_contents = file.take(pe_contents_len);
            pe_contents.read_to_end(&mut contents)?;
            let pe_file = PeFile::from_bytes(&contents)?;

            let path = pe_contents.into_inner().into_path();
            let is_windowed = IMAGE_SUBSYSTEM_WINDOWS_GUI
                == match pe_file.optional_header() {
                    Wrap::T32(header) => header.Subsystem,
                    Wrap::T64(header) => header.Subsystem,
                };

            Ok(Some(Self::Windows { path, is_windowed }))
        } else {
            Ok(None)
        }
    }

    fn re_write(&self, sink: &mut impl Write) -> anyhow::Result<()> {
        match self {
            Self::Posix {
                path,
                shebang_end,
                is_windowed,
                extra_shebang_content,
            } => {
                sink.write_all(if *is_windowed {
                    b"#!pythonw"
                } else {
                    b"#!python"
                })?;
                let mut source = BufReader::new(File::open(path)?);
                source.seek(SeekFrom::Start(*shebang_end as u64))?;
                if let Some(skip) = extra_shebang_content.as_ref() {
                    let coding_line_count = skip.start - shebang_end;
                    if coding_line_count > 0 {
                        let mut coding_line_content = source.take(coding_line_count as u64);
                        io::copy(&mut coding_line_content, sink)?;
                        source = coding_line_content.into_inner()
                    }
                    source.seek(SeekFrom::Start(skip.end as u64))?;
                }
                io::copy(&mut source, sink)?;
            }
            Self::Windows { path, is_windowed } => {
                sink.write_all(if *is_windowed {
                    b"#!pythonw"
                } else {
                    b"#!python"
                })?;
                let mut zip = ZipArchive::new(File::open(path)?)?;
                let mut main_py = zip.by_name("__main__.py")?;
                io::copy(&mut main_py, sink)?;
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use std::borrow::Cow;
    use std::fs;
    use std::io::Cursor;
    use std::path::{Path, PathBuf};
    use std::process::Command;

    use interpreter::Interpreter;
    use python_platform::PythonVersion;
    use rstest::rstest;
    use scripts::{IdentifyInterpreter, Scripts};
    use testing::{embedded_scripts, interpreter_identification_script, python_exe, tmp_dir};

    use crate::Virtualenv;
    use crate::resolver::{InstallPaths, PythonScript, collect_installed_wheels};
    use crate::virtualenv::FileSystemLinker;

    #[rstest]
    fn test_collect_installed_wheels_empty(
        python_exe: &Path,
        interpreter_identification_script: IdentifyInterpreter<'static>,
        tmp_dir: PathBuf,
        mut embedded_scripts: Scripts,
    ) {
        let venv = Virtualenv::create(
            Interpreter::load(python_exe, &interpreter_identification_script).unwrap(),
            Cow::Owned(tmp_dir),
            FileSystemLinker(),
            &mut embedded_scripts,
            false,
            false,
            None,
        )
        .unwrap();

        assert!(collect_installed_wheels(&venv).unwrap().is_empty());
    }

    #[rstest]
    fn test_collect_installed_wheels_uv(tmp_dir: PathBuf, mut embedded_scripts: Scripts) {
        assert!(
            Command::new("uv")
                .args(["venv", "--no-project"])
                .arg(&tmp_dir)
                .spawn()
                .unwrap()
                .wait()
                .unwrap()
                .success()
        );
        assert!(
            Command::new("uv")
                .args(["pip", "install", "--python"])
                .arg(&tmp_dir)
                .args(["greenlet", "dill", "cowsay"])
                .spawn()
                .unwrap()
                .wait()
                .unwrap()
                .success()
        );

        let venv = Virtualenv::load(Cow::Owned(tmp_dir), &mut embedded_scripts).unwrap();
        let installed_wheels = collect_installed_wheels(&venv).unwrap();
        let install_paths = InstallPaths::for_venv(&venv).unwrap();
        for installed_wheel in &installed_wheels {
            installed_wheel
                .pack(&install_paths, Cursor::new(vec![]))
                .unwrap();
        }
    }

    fn detect_python_script(
        chroot: impl AsRef<Path>,
        contents: impl AsRef<[u8]>,
    ) -> (PathBuf, Option<PythonScript>) {
        let script_path = chroot.as_ref().join("script");
        fs::write(&script_path, contents).unwrap();
        let python_script =
            PythonScript::detect(&script_path, PythonVersion::new(3, 14, None)).unwrap();
        (script_path, python_script)
    }

    #[rstest]
    fn test_detect_posix_script_placeholder_shebang(tmp_dir: PathBuf) {
        let (script_path, python_script) = detect_python_script(&tmp_dir, "#!python");
        assert_eq!(
            Some(PythonScript::Posix {
                path: script_path,
                shebang_end: 8,
                is_windowed: false,
                extra_shebang_content: None
            }),
            python_script
        );
        let mut re_written = Vec::new();
        python_script.unwrap().re_write(&mut re_written).unwrap();
        assert_eq!("#!python", String::from_utf8(re_written).unwrap());

        let (script_path, python_script) = detect_python_script(&tmp_dir, "#!python\n");
        assert_eq!(
            Some(PythonScript::Posix {
                path: script_path,
                shebang_end: 8,
                is_windowed: false,
                extra_shebang_content: None
            }),
            python_script
        );
        let mut re_written = Vec::new();
        python_script.unwrap().re_write(&mut re_written).unwrap();
        assert_eq!("#!python\n", String::from_utf8(re_written).unwrap());

        let (script_path, python_script) = detect_python_script(&tmp_dir, "#!pythonw");
        assert_eq!(
            Some(PythonScript::Posix {
                path: script_path,
                shebang_end: 9,
                is_windowed: true,
                extra_shebang_content: None
            }),
            python_script
        );
        let mut re_written = Vec::new();
        python_script.unwrap().re_write(&mut re_written).unwrap();
        assert_eq!("#!pythonw", String::from_utf8(re_written).unwrap());

        let (script_path, python_script) = detect_python_script(tmp_dir, "#!pythonw\n");
        assert_eq!(
            Some(PythonScript::Posix {
                path: script_path,
                shebang_end: 9,
                is_windowed: true,
                extra_shebang_content: None
            }),
            python_script
        );
        let mut re_written = Vec::new();
        python_script.unwrap().re_write(&mut re_written).unwrap();
        assert_eq!("#!pythonw\n", String::from_utf8(re_written).unwrap());
    }

    #[rstest]
    fn test_detect_posix_script_shebang(tmp_dir: PathBuf) {
        let (script_path, python_script) =
            detect_python_script(&tmp_dir, "#!/usr/bin/python\npass");
        assert_eq!(
            Some(PythonScript::Posix {
                path: script_path,
                shebang_end: 17,
                is_windowed: false,
                extra_shebang_content: None
            }),
            python_script
        );
        let mut re_written = Vec::new();
        python_script.unwrap().re_write(&mut re_written).unwrap();
        assert_eq!(
            "#!python\n\
            pass",
            String::from_utf8(re_written).unwrap()
        );

        let (script_path, python_script) =
            detect_python_script(&tmp_dir, "#!/usr/bin/python3\npass");
        assert_eq!(
            Some(PythonScript::Posix {
                path: script_path,
                shebang_end: 18,
                is_windowed: false,
                extra_shebang_content: None
            }),
            python_script
        );
        let mut re_written = Vec::new();
        python_script.unwrap().re_write(&mut re_written).unwrap();
        assert_eq!(
            "#!python\n\
            pass",
            String::from_utf8(re_written).unwrap()
        );

        let (script_path, python_script) =
            detect_python_script(&tmp_dir, "#!/usr/bin/python3.14\npass");
        assert_eq!(
            Some(PythonScript::Posix {
                path: script_path,
                shebang_end: 21,
                is_windowed: false,
                extra_shebang_content: None
            }),
            python_script
        );
        let mut re_written = Vec::new();
        python_script.unwrap().re_write(&mut re_written).unwrap();
        assert_eq!(
            "#!python\n\
            pass",
            String::from_utf8(re_written).unwrap()
        );

        let (_, python_script) = detect_python_script(&tmp_dir, "#!/usr/bin/perl\npass");
        assert!(python_script.is_none())
    }

    #[rstest]
    fn test_detect_posix_script_shebang_with_args(tmp_dir: PathBuf) {
        let (script_path, python_script) =
            detect_python_script(&tmp_dir, "#!/usr/bin/python -I\npass");
        assert_eq!(
            Some(PythonScript::Posix {
                path: script_path,
                shebang_end: 17,
                is_windowed: false,
                extra_shebang_content: None
            }),
            python_script
        );
        let mut re_written = Vec::new();
        python_script.unwrap().re_write(&mut re_written).unwrap();
        assert_eq!(
            "#!python -I\n\
            pass",
            String::from_utf8(re_written).unwrap()
        );

        let (script_path, python_script) =
            detect_python_script(&tmp_dir, "#!/usr/bin/python3 -I\npass");
        assert_eq!(
            Some(PythonScript::Posix {
                path: script_path,
                shebang_end: 18,
                is_windowed: false,
                extra_shebang_content: None
            }),
            python_script
        );
        let mut re_written = Vec::new();
        python_script.unwrap().re_write(&mut re_written).unwrap();
        assert_eq!(
            "#!python -I\n\
            pass",
            String::from_utf8(re_written).unwrap()
        );

        let (script_path, python_script) =
            detect_python_script(&tmp_dir, "#!/usr/bin/python3.14 -I\npass");
        assert_eq!(
            Some(PythonScript::Posix {
                path: script_path,
                shebang_end: 21,
                is_windowed: false,
                extra_shebang_content: None
            }),
            python_script
        );
        let mut re_written = Vec::new();
        python_script.unwrap().re_write(&mut re_written).unwrap();
        assert_eq!(
            "#!python -I\n\
            pass",
            String::from_utf8(re_written).unwrap()
        );

        let (_, python_script) = detect_python_script(&tmp_dir, "#!/usr/bin/perl -n\npass");
        assert!(python_script.is_none())
    }

    #[rstest]
    fn test_detect_bin_sh_redirector_script_shebang(tmp_dir: PathBuf) {
        let (script_path, python_script) = detect_python_script(
            &tmp_dir,
            "#!/bin/sh\n\
            '''exec' /the/venv/bin/python \"$0\" \"$@\"\n\
            '''\n\
            pass",
        );
        assert_eq!(
            Some(PythonScript::Posix {
                path: script_path,
                shebang_end: 9,
                is_windowed: false,
                extra_shebang_content: Some(9..53)
            }),
            python_script
        );
        let mut re_written = Vec::new();
        python_script.unwrap().re_write(&mut re_written).unwrap();
        assert_eq!(
            "#!python\n\
            pass",
            String::from_utf8(re_written).unwrap()
        );

        let (script_path, python_script) = detect_python_script(
            &tmp_dir,
            "#!/bin/sh\n\
            # coding=utf-8\n\
            '''exec' /the/venv/bin/python \"$0\" \"$@\"\n\
            '''\n\
            pass",
        );
        assert_eq!(
            Some(PythonScript::Posix {
                path: script_path,
                shebang_end: 9,
                is_windowed: false,
                extra_shebang_content: Some(24..68)
            }),
            python_script
        );
        let mut re_written = Vec::new();
        python_script.unwrap().re_write(&mut re_written).unwrap();
        assert_eq!(
            "#!python\n\
            # coding=utf-8\n\
            pass",
            String::from_utf8(re_written).unwrap()
        );

        let (script_path, python_script) = detect_python_script(
            &tmp_dir,
            "#!/bin/sh\n\
            '''': pshprs\n\
            /the/venv/bin/python \"$0\" \"$@\"\n\
            '''\n\
            pass",
        );
        assert_eq!(
            Some(PythonScript::Posix {
                path: script_path,
                shebang_end: 9,
                is_windowed: false,
                extra_shebang_content: Some(9..57)
            }),
            python_script
        );
        let mut re_written = Vec::new();
        python_script.unwrap().re_write(&mut re_written).unwrap();
        assert_eq!(
            "#!python\n\
            pass",
            String::from_utf8(re_written).unwrap()
        );

        let (script_path, python_script) = detect_python_script(
            &tmp_dir,
            "#!/bin/sh\n\
            # -*- coding: windows-1252 -*-\n\
            '''': pshprs\n\
            /the/venv/bin/python \"$0\" \"$@\"\n\
            '''\n\
            pass",
        );
        assert_eq!(
            Some(PythonScript::Posix {
                path: script_path,
                shebang_end: 9,
                is_windowed: false,
                extra_shebang_content: Some(40..88)
            }),
            python_script
        );
        let mut re_written = Vec::new();
        python_script.unwrap().re_write(&mut re_written).unwrap();
        assert_eq!(
            "#!python\n\
            # -*- coding: windows-1252 -*-\n\
            pass",
            String::from_utf8(re_written).unwrap()
        )
    }
}
