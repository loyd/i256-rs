//! Print our benchmark results in a line-by-line format, grouped by
//! the bench group.

use std::path::{Path, PathBuf};
use std::{env, ffi, fs, io};

use owo_colors::{OwoColorize, Stream::Stdout};
use serde::Deserialize;

#[allow(dead_code)]
#[derive(Clone, Debug, Deserialize)]
struct Estimates {
    mean: Estimate,
    median: Option<Estimate>,
    slope: Option<Estimate>,
    #[serde(default)]
    median_abs_dev: Option<Estimate>,
    #[serde(default)]
    std_dev: Option<Estimate>,
}

#[allow(dead_code)]
#[derive(Clone, Debug, Deserialize)]
struct Estimate {
    point_estimate: f64,
    standard_error: f64,
    confidence_interval: ConfidenceInterval,
}

#[allow(dead_code)]
#[derive(Clone, Debug, Deserialize)]
struct ConfidenceInterval {
    confidence_level: f64,
    lower_bound: f64,
    upper_bound: f64,
}

#[allow(dead_code)]
#[derive(Clone, Debug, Deserialize)]
struct Benchmark {
    group_id: String,
    title: String,
    function_id: String,
    full_id: String,
    #[serde(default)]
    value_str: Option<String>,
    #[serde(default)]
    throughput: Option<String>,
    #[serde(default)]
    directory_name: Option<String>,
}

fn target_directory() -> io::Result<PathBuf> {
    let target = ffi::OsStr::new("target");
    let mut path = env::current_exe()?;
    while path.file_name() != Some(target) {
        path = path.parent().expect("path must have parent").to_path_buf();
    }

    Ok(path.to_path_buf())
}

fn criterion_directory() -> io::Result<PathBuf> {
    Ok(target_directory()?.join("criterion"))
}

fn file_name(path: &Path) -> &str {
    path.file_name().expect("must have file name").to_str().expect("must be valid UTF-8")
}

fn file_not_found_error(path: &Path) -> io::Error {
    let kind = io::ErrorKind::NotFound;
    io::Error::new(kind, format!("{} not found", file_name(path)))
}

fn get_groups(directory: &Path) -> io::Result<impl Iterator<Item = PathBuf>> {
    let paths = directory
        .read_dir()?
        .map(|x| x.expect("has entry"))
        .filter(|x| x.file_type().expect("has file type").is_dir())
        .filter(|x| x.file_name() != ffi::OsStr::new("report"))
        .map(|x| x.path());
    Ok(paths)
}

fn get_benches(directory: &Path) -> io::Result<impl Iterator<Item = PathBuf>> {
    let paths = directory
        .read_dir()?
        .map(|x| x.expect("has entry"))
        .filter(|x| x.file_type().expect("has file type").is_dir())
        .filter(|x| x.file_name() != ffi::OsStr::new("report"))
        .map(|x| x.path().join("base"));
    Ok(paths)
}

fn read_benchmark(path: &Path) -> io::Result<Benchmark> {
    let benchmark = path.join("benchmark.json");
    let data = fs::read_to_string(benchmark).map_err(|_| file_not_found_error(path))?;
    Ok(serde_json::from_str(&data).unwrap())
}

fn read_estimates(path: &Path) -> io::Result<Estimates> {
    let benchmark = path.join("estimates.json");
    let data = fs::read_to_string(benchmark).map_err(|_| file_not_found_error(path))?;
    Ok(serde_json::from_str(&data).unwrap())
}

fn human_number(value: f64) -> String {
    const MICROS: f64 = 1_000f64;
    const MILLIS: f64 = 1_000_000f64;
    const SECS: f64 = 1_000_000_000f64;
    if value < MICROS {
        format!("{value:.3} ns")
    } else if value < MILLIS {
        let as_micros = value / MICROS;
        format!("{as_micros:.3} µs")
    } else if value < SECS {
        let as_millis = value / MILLIS;
        format!("{as_millis:.3} ms")
    } else {
        // assume seconds
        let as_secs = value / SECS;
        format!("{as_secs:.3}  s")
    }
}

pub fn main() -> io::Result<()> {
    // read benches
    let mut benches = vec![];
    let directory = criterion_directory()?;
    for group in get_groups(&directory)? {
        for bench in get_benches(&group)? {
            let benchmark = read_benchmark(&bench)?;
            let estimates = read_estimates(&bench)?;
            benches.push((benchmark, estimates));
        }
    }

    // print padded benches
    if benches.is_empty() {
        return Ok(());
    }
    let max_title = benches
        .iter()
        .map(|x| &x.0.title)
        .max_by_key(|x| x.len())
        .expect("must have a maxium benchmark");
    let max_length = max_title.len();
    for (benchmark, estimates) in benches {
        let metric = estimates.slope.unwrap_or(estimates.mean);
        let estimate = human_number(metric.point_estimate);
        let lower = human_number(metric.confidence_interval.lower_bound);
        let upper = human_number(metric.confidence_interval.upper_bound);
        let error = human_number(metric.standard_error);
        // want something like: group/bench:  74.224 µs +/- 10ns (74.053 µs, 74.440 µs)
        println!(
            "{:width$}: {} ± {error} ({}, {})",
            benchmark.title.if_supports_color(Stdout, |text| text.cyan()),
            estimate.if_supports_color(Stdout, |text| text.yellow()),
            lower.if_supports_color(Stdout, |text| text.dimmed()),
            upper.if_supports_color(Stdout, |text| text.dimmed()),
            width = max_length,
        );
    }
    Ok(())
}
