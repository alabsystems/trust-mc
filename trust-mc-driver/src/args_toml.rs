// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT

use anyhow::{Result, bail};
use clap::Parser;
use std::collections::BTreeMap;
use std::ffi::OsString;
use std::path::PathBuf;
use std::process::Command;
use std::time::Duration;
use toml::Value;
use toml::value::Table;

use crate::session::{DEFAULT_TOOL_TIMEOUT_SECS, run_piped_with_timeout};

/// Produce the list of arguments to pass to ourself (cargo-kani).
///
/// The arguments passed via command line have precedence over the ones from the Cargo.toml.
pub(crate) fn join_args(input_args: Vec<OsString>) -> Result<Vec<OsString>> {
    let toml_path = cargo_locate_project(&input_args);
    if toml_path.is_err() {
        // We're not inside a Cargo project. Don't error... yet.
        return Ok(input_args);
    }
    let file = std::fs::read_to_string(toml_path?)?;
    let kani_args = toml_to_args(&file)?;
    merge_args(input_args, kani_args)
}

/// Join the arguments passed via command line with the ones found in the Cargo.toml.
///
/// The arguments passed via command line have precedence over the ones from the Cargo.toml.
/// Config args are injected before command line args so CLI takes precedence.
///
/// This function will return the arguments in the following order:
/// ```text
/// <bin_name> [<cfg_kani_args>]* [<cmd_kani_args>]*
/// ```
fn merge_args(cmd_args: Vec<OsString>, cfg_kani_args: Vec<OsString>) -> Result<Vec<OsString>> {
    let bin_name = cmd_args
        .first()
        .ok_or_else(|| anyhow::anyhow!("Expected binary path as first argument"))?
        .clone();
    let mut merged_args = vec![bin_name];
    merged_args.extend(cfg_kani_args);
    merged_args.extend_from_slice(&cmd_args[1..]);
    Ok(merged_args)
}

/// `locate-project` produces a response like: `/full/path/to/src/cargo-kani/Cargo.toml`
fn cargo_locate_project(input_args: &[OsString]) -> Result<PathBuf> {
    // Try parsing our command line arguments as they presently look, to see if a "manifest-path" has been given.
    let current_args = crate::args::CargoKaniArgs::parse_from(input_args);

    if let Some(path) = current_args.verify_opts.cargo.manifest_path {
        Ok(path)
    } else {
        // Use timeout protection (#995)
        let cmd = Command::new("cargo");
        let mut cmd = cmd;
        cmd.args(["locate-project", "--message-format", "plain"]);
        let output = run_piped_with_timeout(cmd, Duration::from_secs(DEFAULT_TOOL_TIMEOUT_SECS))?;
        if !output.status.success() {
            let err = std::str::from_utf8(&output.stderr)?;
            bail!("{}", err);
        }
        let path = std::str::from_utf8(&output.stdout)?;
        // A trim is essential: remove the trailing newline
        Ok(path.trim().into())
    }
}

/// Parse a config toml string and extract the trust-mc arguments we should try injecting.
/// We currently support the following entries:
/// - flags: Flags that get directly passed to trust_mc.
/// - unstable: Unstable features (it will be passed using `-Z` flag).
///
/// The tables supported are:
/// - "workspace.metadata.kani"
/// - "package.metadata.kani"
/// - "kani"
fn toml_to_args(tomldata: &str) -> Result<Vec<OsString>> {
    let config = tomldata.parse::<Table>()?;
    // To make testing easier, our function contract is to produce a stable ordering of flags for a given input.
    // Consequently, we use BTreeMap instead of HashMap here.
    let mut map: BTreeMap<String, Value> = BTreeMap::new();
    let tables = ["workspace.metadata.kani", "package.metadata.kani", "kani"];
    let mut args = Vec::new();

    for table in tables {
        if let Some(table) = get_table(&config, table) {
            if let Some(entry) = table.get("flags")
                && let Some(val) = entry.as_table()
            {
                map.extend(val.iter().map(|(x, y)| (x.to_owned(), y.to_owned())));
            }

            if let Some(entry) = table.get("unstable")
                && let Some(val) = entry.as_table()
            {
                args.append(
                    &mut val
                        .iter()
                        .filter_map(|(k, v)| unstable_entry(k, v).transpose())
                        .collect::<Result<Vec<_>>>()?,
                );
            }
        }
    }

    for (flag, value) in map {
        insert_arg_from_toml(&flag, &value, &mut args)?;
    }

    Ok(args)
}

/// Parse an entry from the unstable table and convert it into a `-Z <unstable_feature>` argument
fn unstable_entry(name: &str, value: &Value) -> Result<Option<OsString>> {
    match value {
        Value::Boolean(b) if *b => Ok(Some(OsString::from(format!("-Z{name}")))),
        Value::Boolean(b) if !b => Ok(None),
        _ => bail!("Expected no arguments for unstable feature `{name}` but found `{value}`"),
    }
}

/// Translates one toml entry (flag, value) into arguments and inserts it into `args`
fn insert_arg_from_toml(flag: &str, value: &Value, args: &mut Vec<OsString>) -> Result<()> {
    match value {
        Value::Boolean(b) => {
            if *b {
                args.push(format!("--{flag}").into());
            } else if flag.starts_with("no-") {
                // Seems iffy. Let's just not support this.
                bail!("{} disables a disabling flag. Just enable the flag instead.", flag);
            } else {
                args.push(format!("--no-{flag}").into());
            }
        }
        Value::Array(a) => {
            for arg in a {
                if let Some(arg) = arg.as_str() {
                    args.push(format!("--{flag}").into());
                    args.push(arg.into());
                } else {
                    bail!("flag {} contains non-string values", flag);
                }
            }
        }
        Value::String(s) => {
            args.push(format!("--{flag}").into());
            args.push(s.into());
        }
        _ => {
            bail!("Unknown key type {}", flag);
        }
    }
    Ok(())
}

/// Take 'a.b.c' and turn it into 'start['a']['b']['c']' reliably, and interpret the result as a table
fn get_table<'a>(start: &'a Table, table: &str) -> Option<&'a Table> {
    let mut current = Some(start);
    for key in table.split('.') {
        current = current.and_then(|t| t.get(key).and_then(|v| v.as_table()));
    }
    current
}

#[cfg(test)]
mod tests {
    use std::str::FromStr;

    use super::*;

    #[test]
    fn check_toml_parsing() {
        let a = "[workspace.metadata.kani]
                      flags = { default-checks = false, default-unwind = \"2\" }";
        let b = toml_to_args(a).unwrap();
        // default first, then unwind thanks to btree ordering.
        assert_eq!(b, vec!["--no-default-checks", "--default-unwind", "2"]);
    }

    #[test]
    fn check_merge_args_with_only_command_line_args() {
        let cmd_args: Vec<OsString> =
            ["cargo_kani", "--no-default-checks", "--default-unwind", "2"]
                .iter()
                .map(|&s| s.into())
                .collect();
        let merged = merge_args(cmd_args.clone(), Vec::new()).unwrap();
        assert_eq!(merged, cmd_args);
    }

    #[test]
    fn check_merge_args_with_only_config_kani_args() {
        let cfg_args: Vec<OsString> =
            ["--no-default-checks", "--default-unwind", "2"].iter().map(|&s| s.into()).collect();
        let merged = merge_args(vec!["kani".into()], cfg_args.clone()).unwrap();
        assert_eq!(merged[0], OsString::from("kani"));
        assert_eq!(merged[1..], cfg_args);
    }

    #[test]
    fn check_merge_args_order() {
        let cmd_args: Vec<OsString> = vec!["kani".into(), "--debug".into()];
        let cfg_kani_args: Vec<OsString> = vec!["--no-default-checks".into()];
        let merged = merge_args(cmd_args.clone(), cfg_kani_args.clone()).unwrap();
        assert_eq!(merged.len(), cmd_args.len() + cfg_kani_args.len());
        assert_eq!(merged[0], OsString::from("kani"));
        assert_eq!(merged[1], OsString::from("--no-default-checks"));
        assert_eq!(merged[2], OsString::from("--debug"));
    }

    #[test]
    fn check_multiple_table_works() {
        let data = "[workspace.metadata.kani.unstable]
                         disabled-feature=false
                         enabled-feature=true
                         [workspace.metadata.kani.flags]
                         kani-arg=\"value\"";
        let kani_args = toml_to_args(data).unwrap();
        assert_eq!(kani_args, vec!["-Zenabled-feature", "--kani-arg", "value"]);
    }

    #[test]
    fn check_unstable_table_works() {
        let data = "[workspace.metadata.kani.unstable]
                         disabled-feature=false
                         enabled-feature=true";
        let kani_args = toml_to_args(data).unwrap();
        assert_eq!(kani_args, vec!["-Zenabled-feature"]);
    }

    #[test]
    fn check_unstable_entry_enabled() -> Result<()> {
        let name = String::from("feature");
        assert_eq!(
            unstable_entry(&name, &Value::Boolean(true))?,
            Some(OsString::from_str("-Zfeature")?)
        );
        Ok(())
    }

    #[test]
    fn check_unstable_entry_disabled() -> Result<()> {
        let name = String::from("feature");
        assert_eq!(unstable_entry(&name, &Value::Boolean(false))?, None);
        Ok(())
    }

    #[test]
    fn check_unstable_entry_invalid() {
        let name = String::from("feature");
        assert!(unstable_entry(&name, &Value::String(String::new())).is_err());
    }
}
