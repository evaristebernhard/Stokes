use degree08::{
    D4EventSearchOptions, D4GeneratedCandidate, D4SearchCandidate,
    endrass_multi_prime_calibrations, endrass_parameters_mod_p, generate_d4_event_candidates,
    scan_d4_local_window,
};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct D4WindowConfig {
    prime: i64,
    radius: i64,
    limit: usize,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct D4EventsConfig {
    prime: i64,
    max_event_set_size: usize,
    max_free_dimension: usize,
    solution_scan_limit: usize,
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
        Some("d4-events") => {
            run_d4_events(parse_d4_events_args(&args[1..])?);
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

fn run_d4_events(config: D4EventsConfig) {
    match config.prime {
        31 => print_generated_candidates(
            generate_d4_event_candidates(endrass_parameters_mod_p::<31>(8), config.options()),
            config.format,
        ),
        41 => print_generated_candidates(
            generate_d4_event_candidates(endrass_parameters_mod_p::<41>(17), config.options()),
            config.format,
        ),
        73 => print_generated_candidates(
            generate_d4_event_candidates(endrass_parameters_mod_p::<73>(32), config.options()),
            config.format,
        ),
        89 => print_generated_candidates(
            generate_d4_event_candidates(endrass_parameters_mod_p::<89>(25), config.options()),
            config.format,
        ),
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

fn print_generated_candidates<const P: i64>(
    candidates: Vec<D4GeneratedCandidate<P>>,
    format: OutputFormat,
) {
    match format {
        OutputFormat::Tsv => {
            println!("{}", D4GeneratedCandidate::<P>::tsv_header());
            for candidate in candidates {
                println!("{}", candidate.to_tsv());
            }
        }
        OutputFormat::Json => {
            for candidate in candidates {
                println!("{}", candidate.to_json_line());
            }
        }
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

    validate_prime(config.prime)?;
    if config.radius < 0 {
        return Err("--radius must be non-negative".to_string());
    }
    if config.limit == 0 {
        return Err("--limit must be positive".to_string());
    }
    Ok(config)
}

fn parse_d4_events_args(args: &[String]) -> Result<D4EventsConfig, String> {
    let mut config = D4EventsConfig {
        prime: 31,
        max_event_set_size: 2,
        max_free_dimension: 1,
        solution_scan_limit: 200,
        limit: 20,
        format: OutputFormat::Tsv,
    };
    let mut index = 0;
    while index < args.len() {
        let value = args
            .get(index + 1)
            .ok_or_else(|| format!("missing value for `{}`", args[index]))?;
        match args[index].as_str() {
            "--prime" => config.prime = parse_i64("--prime", value)?,
            "--max-event-set-size" => {
                config.max_event_set_size = parse_usize("--max-event-set-size", value)?
            }
            "--max-free-dim" => config.max_free_dimension = parse_usize("--max-free-dim", value)?,
            "--solution-limit" => {
                config.solution_scan_limit = parse_usize("--solution-limit", value)?
            }
            "--limit" => config.limit = parse_usize("--limit", value)?,
            "--format" => config.format = parse_output_format(value)?,
            option => return Err(format!("unknown d4-events option `{option}`")),
        }
        index += 2;
    }

    validate_prime(config.prime)?;
    if config.max_event_set_size == 0 {
        return Err("--max-event-set-size must be positive".to_string());
    }
    if config.solution_scan_limit == 0 {
        return Err("--solution-limit must be positive".to_string());
    }
    if config.limit == 0 {
        return Err("--limit must be positive".to_string());
    }
    Ok(config)
}

impl D4EventsConfig {
    fn options(self) -> D4EventSearchOptions {
        D4EventSearchOptions {
            max_event_set_size: self.max_event_set_size,
            max_free_dimension: self.max_free_dimension,
            solution_scan_limit: self.solution_scan_limit,
            candidate_limit: self.limit,
            ..D4EventSearchOptions::default()
        }
    }
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

fn validate_prime(prime: i64) -> Result<(), String> {
    if matches!(prime, 31 | 41 | 73 | 89) {
        Ok(())
    } else {
        Err(format!("unsupported prime {prime}; use one of 31,41,73,89"))
    }
}

fn usage() -> &'static str {
    "usage:
  search_d4
  search_d4 calibration
  search_d4 d4-window [--prime 31|41|73|89] [--radius N] [--limit N]
  search_d4 d4-events [--prime 31|41|73|89] [--max-event-set-size N] [--max-free-dim N] [--solution-limit N] [--limit N] [--format tsv|json]"
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

    #[test]
    fn d4_events_args_parse_generation_controls() {
        assert_eq!(
            parse_d4_events_args(&args(&[
                "--prime",
                "41",
                "--max-event-set-size",
                "3",
                "--max-free-dim",
                "1",
                "--solution-limit",
                "50",
                "--limit",
                "5",
                "--format",
                "json"
            ]))
            .unwrap(),
            D4EventsConfig {
                prime: 41,
                max_event_set_size: 3,
                max_free_dimension: 1,
                solution_scan_limit: 50,
                limit: 5,
                format: OutputFormat::Json
            }
        );
    }

    #[test]
    fn d4_events_args_reject_bad_inputs() {
        assert!(parse_d4_events_args(&args(&["--prime", "97"])).is_err());
        assert!(parse_d4_events_args(&args(&["--max-event-set-size", "0"])).is_err());
        assert!(parse_d4_events_args(&args(&["--solution-limit", "0"])).is_err());
        assert!(parse_d4_events_args(&args(&["--format", "xml"])).is_err());
    }
}
