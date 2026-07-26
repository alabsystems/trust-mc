// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(dead_code)]
use serde::{Deserialize, Serialize};
use std::path::{Path, PathBuf};
use std::time::Duration;

#[derive(Debug, Serialize, Deserialize)]
pub(crate) struct AggrResult {
    pub(crate) krate: PathBuf,
    pub(crate) krate_trimmed_path: String,
    /// the stats for only the 25th-75th percentile of runs on this crate, i.e., the interquartile range
    pub(crate) iqr_stats: Stats,
    /// the stats for all runs on this crate
    full_stats: Stats,
}

pub(crate) fn krate_trimmed_path(krate: &Path) -> String {
    format!(
        "{:?}",
        krate
            .canonicalize()
            .unwrap()
            .strip_prefix(std::env::current_dir().unwrap().parent().unwrap())
            .unwrap()
    )
}

impl AggrResult {
    pub(crate) fn new(krate: PathBuf, iqr_stats: Stats, full_stats: Stats) -> Self {
        AggrResult { krate_trimmed_path: krate_trimmed_path(&krate), krate, iqr_stats, full_stats }
    }

    pub(crate) fn full_std_dev(&self) -> Duration {
        self.full_stats.std_dev
    }

    pub(crate) fn iqr(&self) -> Duration {
        self.iqr_stats.range.1 - self.iqr_stats.range.0
    }
}

#[derive(Debug, Serialize, Deserialize)]
pub(crate) struct Stats {
    pub(crate) avg: Duration,
    pub(crate) std_dev: Duration,
    pub(crate) range: (Duration, Duration),
}

/// Sum the IQR averages and IQR standard deviations respectively for all crates timed.
pub(crate) fn aggregate_aggregates(info: &[AggrResult]) -> (Duration, Duration) {
    for i in info {
        println!("krate {:?} -- {:?}", i.krate, i.iqr_stats.avg);
    }

    (info.iter().map(|i| i.iqr_stats.avg).sum(), info.iter().map(|i| i.iqr_stats.std_dev).sum())
}

pub(crate) fn fraction_of_duration(dur: Duration, frac: f64) -> Duration {
    Duration::from_nanos(((dur.as_nanos() as f64) * frac) as u64)
}
