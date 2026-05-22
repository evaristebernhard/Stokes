use degree08::{
    D4SearchCandidate, endrass_multi_prime_calibrations, endrass_parameters_mod_p,
    scan_d4_local_window,
};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct D4WindowConfig {
    prime: i64,
    radius: i64,
    limit: usize,
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
    match args.first().map(String::as_str) {
        None | Some("calibration") => {
            if args.len() > 1 {
                return Err("calibration does not accept extra arguments".to_string());
            }
            run_calibration();
            Ok(())
        }
        Some("d4-window") => {
            run_d4_window(parse_d4_window_args(&args[1..])?);
            Ok(())
        }
        Some("-h" | "--help" | "help") => {
            println!("{}", usage());
            Ok(())
        }
        Some(command) => Err(format!("unknown command `{command}`")),
    }
}

fn run_calibration() {
    println!(
        "prime\tsqrt2\tglobal_visible_nodes\tglobal_bad\tbase_ac\tbase_visible\tsegre_event_weight"
    );
    for calibration in endrass_multi_prime_calibrations() {
        println!(
            "{}\t{}\t{}\t{}\t{}\t{}\t{}",
            calibration.prime(),
            calibration.sqrt2(),
            calibration.global_visible_nodes(),
            calibration.global_bad_singularities(),
            calibration.base_algebraic_closure_length(),
            calibration.base_visible_roots(),
            calibration.segre_event_orbit_contribution()
        );
    }
}

fn run_d4_window(config: D4WindowConfig) {
    match config.prime {
        31 => print_candidates(scan_d4_local_window(
            endrass_parameters_mod_p::<31>(8),
            config.radius,
            config.limit,
        )),
        41 => print_candidates(scan_d4_local_window(
            endrass_parameters_mod_p::<41>(17),
            config.radius,
            config.limit,
        )),
        73 => print_candidates(scan_d4_local_window(
            endrass_parameters_mod_p::<73>(32),
            config.radius,
            config.limit,
        )),
        89 => print_candidates(scan_d4_local_window(
            endrass_parameters_mod_p::<89>(25),
            config.radius,
            config.limit,
        )),
        _ => {
            unreachable!("unsupported prime was rejected by argument parsing");
        }
    }
}

fn print_candidates<const P: i64>(candidates: Vec<D4SearchCandidate<P>>) {
    println!("{}", D4SearchCandidate::<P>::tsv_header());
    for candidate in candidates {
        println!("{}", candidate.to_tsv());
    }
}

fn parse_d4_window_args(args: &[String]) -> Result<D4WindowConfig, String> {
    let mut config = D4WindowConfig {
        prime: 31,
        radius: 1,
        limit: 10,
    };
    let mut index = 0;
    while index < args.len() {
        let value = args
            .get(index + 1)
            .ok_or_else(|| format!("missing value for `{}`", args[index]))?;
        match args[index].as_str() {
            "--prime" => config.prime = parse_i64("--prime", value)?,
            "--radius" => config.radius = parse_i64("--radius", value)?,
            "--limit" => config.limit = parse_usize("--limit", value)?,
            option => return Err(format!("unknown d4-window option `{option}`")),
        }
        index += 2;
    }

    if !matches!(config.prime, 31 | 41 | 73 | 89) {
        return Err(format!(
            "unsupported prime {}; use one of 31,41,73,89",
            config.prime
        ));
    }
    if config.radius < 0 {
        return Err("--radius must be non-negative".to_string());
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

fn usage() -> &'static str {
    "usage:
  search_d4
  search_d4 calibration
  search_d4 d4-window [--prime 31|41|73|89] [--radius N] [--limit N]"
}

#[cfg(test)]
mod tests {
    use super::*;

    fn args(values: &[&str]) -> Vec<String> {
        values.iter().map(|value| value.to_string()).collect()
    }

    #[test]
    fn d4_window_args_have_checked_defaults() {
        assert_eq!(
            parse_d4_window_args(&args(&[])).unwrap(),
            D4WindowConfig {
                prime: 31,
                radius: 1,
                limit: 10
            }
        );
    }

    #[test]
    fn d4_window_args_parse_supported_prime_radius_and_limit() {
        assert_eq!(
            parse_d4_window_args(&args(&["--prime", "89", "--radius", "0", "--limit", "1"]))
                .unwrap(),
            D4WindowConfig {
                prime: 89,
                radius: 0,
                limit: 1
            }
        );
    }

    #[test]
    fn d4_window_args_reject_bad_inputs() {
        assert!(parse_d4_window_args(&args(&["--prime", "abc"])).is_err());
        assert!(parse_d4_window_args(&args(&["--prime", "97"])).is_err());
        assert!(parse_d4_window_args(&args(&["--radius", "-1"])).is_err());
        assert!(parse_d4_window_args(&args(&["--limit", "0"])).is_err());
        assert!(parse_d4_window_args(&args(&["--prime"])).is_err());
    }
}
