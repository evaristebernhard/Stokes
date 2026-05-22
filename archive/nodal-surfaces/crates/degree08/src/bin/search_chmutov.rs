use degree08::{
    Fp, PolynomialP3Fp,
    search_core::{
        ExperimentRecord, ProjectiveLinearMap, ProjectiveSurfaceScorerInput, SurfaceSymmetry,
        score_projective_surface,
    },
};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct ChmutovConfig {
    prime: i64,
    lambda_start: i64,
    lambda_end: i64,
    limit: usize,
    format: OutputFormat,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum OutputFormat {
    Tsv,
    Json,
}

fn main() {
    let args = std::env::args().skip(1).collect::<Vec<_>>();
    if let Err(message) = run(&args) {
        eprintln!("{message}");
        eprintln!("{}", usage());
        std::process::exit(2);
    }
}

fn run(args: &[String]) -> Result<(), String> {
    if matches!(
        args.first().map(String::as_str),
        Some("-h" | "--help" | "help")
    ) {
        println!("{}", usage());
        return Ok(());
    }

    let config = parse_args(args)?;
    match config.prime {
        31 => print_records(scan_chmutov::<31>(config), config.format),
        _ => unreachable!("unsupported prime was rejected by argument parsing"),
    }
    Ok(())
}

fn scan_chmutov<const P: i64>(config: ChmutovConfig) -> Vec<(isize, i64, ExperimentRecord)> {
    let mut records = (config.lambda_start..=config.lambda_end)
        .map(|lambda_value| {
            let polynomial = chmutov_t8_surface(Fp::<P>::new(lambda_value));
            let input = ProjectiveSurfaceScorerInput::new(polynomial)
                .with_symmetry(even_coordinate_s3_symmetry());
            let stats = score_projective_surface(&input);
            let score = stats.node_like() as isize - 4 * stats.bad_sing() as isize;
            let record = ExperimentRecord::from_stats(
                "chmutov-t8-sum",
                format!("lambda={}", Fp::<P>::new(lambda_value).value()),
                score,
                &stats,
            )
            .with_tag("model", "C8(x,w)+C8(y,w)+C8(z,w)+lambda*w^8")
            .with_tag("lambda", Fp::<P>::new(lambda_value).value().to_string())
            .with_tag("symmetry", "even-coordinate-signs-semidirect-S3")
            .with_tag("orbit_profile", format_orbit_profile(stats.orbit_profile()))
            .with_tag("route", "folding-control");

            (score, lambda_value, record)
        })
        .collect::<Vec<_>>();

    records.sort_by(|left, right| {
        right
            .0
            .cmp(&left.0)
            .then_with(|| left.1.rem_euclid(P).cmp(&right.1.rem_euclid(P)))
    });
    records.truncate(config.limit.min(records.len()));
    records
}

fn print_records(records: Vec<(isize, i64, ExperimentRecord)>, format: OutputFormat) {
    match format {
        OutputFormat::Tsv => {
            println!("{}", ExperimentRecord::tsv_header());
            for (_, _, record) in records {
                println!("{}", record.to_tsv());
            }
        }
        OutputFormat::Json => {
            for (_, _, record) in records {
                println!("{}", record.to_json_line());
            }
        }
    }
}

fn chmutov_t8_surface<const P: i64>(lambda: Fp<P>) -> PolynomialP3Fp<P> {
    let [x, y, z, w] = std::array::from_fn(PolynomialP3Fp::<P>::variable);
    chebyshev_t8_homogeneous(&x, &w)
        .add(&chebyshev_t8_homogeneous(&y, &w))
        .add(&chebyshev_t8_homogeneous(&z, &w))
        .add(&w.pow_usize(8).scale(lambda))
}

fn chebyshev_t8_homogeneous<const P: i64>(
    variable: &PolynomialP3Fp<P>,
    homogenizer: &PolynomialP3Fp<P>,
) -> PolynomialP3Fp<P> {
    monomial_pair(variable, 8, homogenizer, 0, 128)
        .add(&monomial_pair(variable, 6, homogenizer, 2, -256))
        .add(&monomial_pair(variable, 4, homogenizer, 4, 160))
        .add(&monomial_pair(variable, 2, homogenizer, 6, -32))
        .add(&monomial_pair(variable, 0, homogenizer, 8, 1))
}

fn monomial_pair<const P: i64>(
    left: &PolynomialP3Fp<P>,
    left_power: usize,
    right: &PolynomialP3Fp<P>,
    right_power: usize,
    coefficient: i64,
) -> PolynomialP3Fp<P> {
    left.pow_usize(left_power)
        .mul(&right.pow_usize(right_power))
        .scale(Fp::new(coefficient))
}

fn even_coordinate_s3_symmetry<const P: i64>() -> SurfaceSymmetry<P> {
    let z = Fp::new(0);
    let o = Fp::new(1);
    let m = Fp::new(-1);
    SurfaceSymmetry::Explicit(vec![
        ProjectiveLinearMap::new([[z, o, z, z], [o, z, z, z], [z, z, o, z], [z, z, z, o]]),
        ProjectiveLinearMap::new([[o, z, z, z], [z, z, o, z], [z, o, z, z], [z, z, z, o]]),
        ProjectiveLinearMap::new([[m, z, z, z], [z, o, z, z], [z, z, o, z], [z, z, z, o]]),
    ])
}

fn format_orbit_profile(profile: &std::collections::BTreeMap<usize, usize>) -> String {
    if profile.is_empty() {
        return "none".to_string();
    }

    profile
        .iter()
        .map(|(orbit_size, count)| format!("{orbit_size}:{count}"))
        .collect::<Vec<_>>()
        .join(",")
}

fn parse_args(args: &[String]) -> Result<ChmutovConfig, String> {
    let mut config = ChmutovConfig {
        prime: 31,
        lambda_start: 0,
        lambda_end: 30,
        limit: 31,
        format: OutputFormat::Tsv,
    };

    let mut index = 0;
    while index < args.len() {
        let value = args
            .get(index + 1)
            .ok_or_else(|| format!("missing value for `{}`", args[index]))?;
        match args[index].as_str() {
            "--prime" => config.prime = parse_i64("--prime", value)?,
            "--lambda" => {
                let lambda = parse_i64("--lambda", value)?;
                config.lambda_start = lambda;
                config.lambda_end = lambda;
            }
            "--lambda-start" => config.lambda_start = parse_i64("--lambda-start", value)?,
            "--lambda-end" => config.lambda_end = parse_i64("--lambda-end", value)?,
            "--limit" => config.limit = parse_usize("--limit", value)?,
            "--format" => config.format = parse_output_format(value)?,
            option => return Err(format!("unknown option `{option}`")),
        }
        index += 2;
    }

    validate_config(config)
}

fn validate_config(config: ChmutovConfig) -> Result<ChmutovConfig, String> {
    if config.prime != 31 {
        return Err(format!(
            "unsupported prime {}; Worker B prototype currently supports p=31",
            config.prime
        ));
    }
    if config.lambda_start < 0 || config.lambda_start >= config.prime {
        return Err(format!(
            "--lambda-start must lie in 0..{}",
            config.prime - 1
        ));
    }
    if config.lambda_end < 0 || config.lambda_end >= config.prime {
        return Err(format!("--lambda-end must lie in 0..{}", config.prime - 1));
    }
    if config.lambda_start > config.lambda_end {
        return Err("--lambda-start must be <= --lambda-end".to_string());
    }
    if config.limit == 0 {
        return Err("--limit must be positive".to_string());
    }
    Ok(config)
}

fn parse_i64(name: &str, value: &str) -> Result<i64, String> {
    value
        .parse()
        .map_err(|_| format!("invalid integer for `{name}`: `{value}`"))
}

fn parse_usize(name: &str, value: &str) -> Result<usize, String> {
    value
        .parse()
        .map_err(|_| format!("invalid positive integer for `{name}`: `{value}`"))
}

fn parse_output_format(value: &str) -> Result<OutputFormat, String> {
    match value {
        "tsv" => Ok(OutputFormat::Tsv),
        "json" | "jsonl" => Ok(OutputFormat::Json),
        _ => Err(format!("invalid output format `{value}`; use tsv or json")),
    }
}

fn usage() -> &'static str {
    "usage:
  search_chmutov [--prime 31] [--lambda N | --lambda-start A --lambda-end B] [--limit N] [--format tsv|json]

Scans the finite-field control family
  C8(x,w)+C8(y,w)+C8(z,w)+lambda*w^8
where C8 is the homogeneous Chebyshev T8 polynomial."
}

#[cfg(test)]
mod tests {
    use super::*;

    fn args(values: &[&str]) -> Vec<String> {
        values.iter().map(|value| value.to_string()).collect()
    }

    #[test]
    fn args_have_checked_defaults() {
        assert_eq!(
            parse_args(&args(&[])).unwrap(),
            ChmutovConfig {
                prime: 31,
                lambda_start: 0,
                lambda_end: 30,
                limit: 31,
                format: OutputFormat::Tsv
            }
        );
    }

    #[test]
    fn args_parse_single_lambda_and_json_format() {
        assert_eq!(
            parse_args(&args(&[
                "--lambda", "12", "--limit", "3", "--format", "json"
            ]))
            .unwrap(),
            ChmutovConfig {
                prime: 31,
                lambda_start: 12,
                lambda_end: 12,
                limit: 3,
                format: OutputFormat::Json
            }
        );
    }

    #[test]
    fn args_reject_bad_ranges_and_primes() {
        assert!(parse_args(&args(&["--prime", "41"])).is_err());
        assert!(parse_args(&args(&["--lambda-start", "10", "--lambda-end", "9"])).is_err());
        assert!(parse_args(&args(&["--lambda", "31"])).is_err());
        assert!(parse_args(&args(&["--limit", "0"])).is_err());
    }

    #[test]
    fn chmutov_surface_is_homogeneous_degree_eight() {
        let polynomial = chmutov_t8_surface::<31>(Fp::new(7));
        assert_eq!(polynomial.degree(), 8);
        assert!(polynomial.is_homogeneous());
    }
}
