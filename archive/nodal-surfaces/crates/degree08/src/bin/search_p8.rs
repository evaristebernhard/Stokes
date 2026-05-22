use degree08::Fp;
use degree08::search_core::{
    ExperimentRecord, PlaneFp, PlaneProductSkeleton, ProjectiveSurfaceScorerInput,
    SurfacePolynomialFp, SurfaceSymmetry, score_projective_surface,
};
use nodal_core::Matrix;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct P8Config {
    prime: i64,
    limit: usize,
    format: OutputFormat,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum OutputFormat {
    Tsv,
    Json,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct P8Candidate<const P: i64> {
    label: String,
    arrangement: &'static str,
    r_model: &'static str,
    params: (i64, i64, i64),
    planes: Vec<PlaneFp<P>>,
    quartic_r: SurfacePolynomialFp<P>,
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
    let config = parse_args(args)?;
    match config.prime {
        31 => print_records(scan_p8_mod_prime::<31>(config.limit), config.format),
        _ => unreachable!("unsupported prime was rejected by argument parsing"),
    }
    Ok(())
}

fn print_records(records: Vec<ExperimentRecord>, format: OutputFormat) {
    match format {
        OutputFormat::Tsv => {
            println!("{}", ExperimentRecord::tsv_header());
            for record in records {
                println!("{}", record.to_tsv());
            }
        }
        OutputFormat::Json => {
            for record in records {
                println!("{}", record.to_json_line());
            }
        }
    }
}

fn scan_p8_mod_prime<const P: i64>(limit: usize) -> Vec<ExperimentRecord> {
    let mut records = candidate_pool::<P>()
        .into_iter()
        .filter_map(score_candidate)
        .collect::<Vec<_>>();
    records.sort_by(|left, right| {
        right
            .sort_key
            .cmp(&left.sort_key)
            .then_with(|| left.to_tsv().cmp(&right.to_tsv()))
    });
    records.truncate(limit);
    records.into_iter().map(|record| record.record).collect()
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct ScoredExperimentRecord {
    sort_key: (isize, usize, usize),
    record: ExperimentRecord,
}

impl ScoredExperimentRecord {
    fn to_tsv(&self) -> String {
        self.record.to_tsv()
    }
}

fn score_candidate<const P: i64>(candidate: P8Candidate<P>) -> Option<ScoredExperimentRecord> {
    let arrangement_quality = arrangement_quality(&candidate.planes);
    if !arrangement_quality.simple {
        return None;
    }

    let skeleton = PlaneProductSkeleton::new(candidate.planes.clone(), candidate.quartic_r.clone());
    let line_stats = skeleton.base_line_length_stats();
    if !line_stats.all_lines_degree_four_squarefree() || line_stats.triple_plane_bad_points() != 0 {
        return None;
    }

    let polynomial = skeleton.p8_minus_r4_squared(Fp::new(1));
    let input = ProjectiveSurfaceScorerInput::new(polynomial)
        .with_plane_product_skeleton(skeleton)
        .with_symmetry(SurfaceSymmetry::None);
    let stats = score_projective_surface(&input);
    let score = stats.node_like() as isize - 8 * stats.bad_sing() as isize
        + line_stats.algebraic_closure_length() as isize;

    let node_like = stats.node_like();
    let bad_sing = stats.bad_sing();
    let base_visible = line_stats.visible_root_count();
    let record = ExperimentRecord::from_stats("p8-general", candidate.label, score, &stats)
        .with_tag("arrangement", candidate.arrangement)
        .with_tag("r_model", candidate.r_model)
        .with_tag(
            "params",
            format!(
                "{},{},{}",
                candidate.params.0, candidate.params.1, candidate.params.2
            ),
        )
        .with_tag("base_ac", line_stats.algebraic_closure_length().to_string())
        .with_tag("base_visible", line_stats.visible_root_count().to_string())
        .with_tag("simple_pairs", arrangement_quality.pair_count.to_string())
        .with_tag(
            "simple_triples",
            arrangement_quality.triple_count.to_string(),
        )
        .with_tag("simple_quads", arrangement_quality.quad_count.to_string())
        .with_tag("orbit_profile", format!("{:?}", stats.orbit_profile()));

    Some(ScoredExperimentRecord {
        sort_key: (score, node_like, base_visible.saturating_sub(bad_sing)),
        record,
    })
}

fn candidate_pool<const P: i64>() -> Vec<P8Candidate<P>> {
    let params = [
        (2, 6, 29),
        (2, 20, 8),
        (2, 21, 13),
        (2, 28, 26),
        (2, 29, 12),
        (3, 12, 28),
        (3, 15, 23),
        (3, 15, 30),
        (3, 16, 12),
        (5, 9, 13),
    ];

    let mut candidates = Vec::new();
    for (index, &(a, b, c)) in params.iter().enumerate() {
        for (arrangement, planes) in [
            ("coord-affine", coord_affine_planes(a, b, c)),
            ("skew-affine", skew_affine_planes(a, b, c)),
        ] {
            candidates.push(P8Candidate {
                label: format!("{arrangement}-even-{index}"),
                arrangement,
                r_model: "even",
                params: (a, b, c),
                planes: planes.clone(),
                quartic_r: even_quartic(a, b, c),
            });
            candidates.push(P8Candidate {
                label: format!("{arrangement}-dense-{index}"),
                arrangement,
                r_model: "dense",
                params: (a, b, c),
                planes,
                quartic_r: dense_quartic(a + 2 * b + 3 * c),
            });
        }
    }
    candidates
}

fn coord_affine_planes<const P: i64>(a: i64, b: i64, c: i64) -> Vec<PlaneFp<P>> {
    vec![
        plane([1, 0, 0, 0]),
        plane([0, 1, 0, 0]),
        plane([0, 0, 1, 0]),
        plane([0, 0, 0, 1]),
        plane([1, 1, 1, 1]),
        plane([1, a, b, c]),
        plane([1, b, c + 1, a + 2]),
        plane([1, c + 2, a + 1, b + 3]),
    ]
}

fn skew_affine_planes<const P: i64>(a: i64, b: i64, c: i64) -> Vec<PlaneFp<P>> {
    vec![
        plane([1, 0, a, b]),
        plane([0, 1, b, c]),
        plane([1, 1, a, c + 1]),
        plane([1, -1, b + 1, a]),
        plane([1, a, 0, c]),
        plane([b, 1, c, 0]),
        plane([a, c, 1, b]),
        plane([c, a, b, 1]),
    ]
}

fn plane<const P: i64>(coefficients: [i64; 4]) -> PlaneFp<P> {
    coefficients.map(Fp::new)
}

fn even_quartic<const P: i64>(a: i64, b: i64, c: i64) -> SurfacePolynomialFp<P> {
    polynomial_from_terms(&[
        (1, [4, 0, 0, 0]),
        (1, [0, 4, 0, 0]),
        (1, [0, 0, 4, 0]),
        (1, [0, 0, 0, 4]),
        (a, [2, 2, 0, 0]),
        (b, [2, 0, 2, 0]),
        (c, [2, 0, 0, 2]),
        (c + 1, [0, 2, 2, 0]),
        (b + 1, [0, 2, 0, 2]),
        (a + 1, [0, 0, 2, 2]),
        (a + b + c, [1, 1, 1, 1]),
    ])
}

fn dense_quartic<const P: i64>(seed: i64) -> SurfacePolynomialFp<P> {
    let mut terms = Vec::new();
    for x in 0..=4 {
        for y in 0..=(4 - x) {
            for z in 0..=(4 - x - y) {
                let w = 4 - x - y - z;
                let weight = 1
                    + seed * (1 + 2 * x as i64 + 3 * y as i64 + 5 * z as i64 + 7 * w as i64)
                    + (x * y + z * w) as i64;
                terms.push((weight, [x, y, z, w]));
            }
        }
    }
    polynomial_from_terms(&terms)
}

fn polynomial_from_terms<const P: i64>(terms: &[(i64, [usize; 4])]) -> SurfacePolynomialFp<P> {
    SurfacePolynomialFp::from_terms(
        terms
            .iter()
            .map(|(coefficient, exponents)| (Fp::new(*coefficient), *exponents))
            .collect(),
    )
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct ArrangementQuality {
    simple: bool,
    pair_count: usize,
    triple_count: usize,
    quad_count: usize,
}

fn arrangement_quality<const P: i64>(planes: &[PlaneFp<P>]) -> ArrangementQuality {
    let mut simple = true;
    let mut pair_count = 0;
    let mut triple_count = 0;
    let mut quad_count = 0;

    for first in 0..planes.len() {
        for second in (first + 1)..planes.len() {
            if plane_rank(&[planes[first], planes[second]]) != 2 {
                simple = false;
            }
            pair_count += 1;
        }
    }

    for first in 0..planes.len() {
        for second in (first + 1)..planes.len() {
            for third in (second + 1)..planes.len() {
                if plane_rank(&[planes[first], planes[second], planes[third]]) != 3 {
                    simple = false;
                }
                triple_count += 1;
            }
        }
    }

    for first in 0..planes.len() {
        for second in (first + 1)..planes.len() {
            for third in (second + 1)..planes.len() {
                for fourth in (third + 1)..planes.len() {
                    if plane_rank(&[planes[first], planes[second], planes[third], planes[fourth]])
                        != 4
                    {
                        simple = false;
                    }
                    quad_count += 1;
                }
            }
        }
    }

    ArrangementQuality {
        simple,
        pair_count,
        triple_count,
        quad_count,
    }
}

fn plane_rank<const P: i64>(planes: &[PlaneFp<P>]) -> usize {
    Matrix::from_rows(planes.iter().map(|plane| plane.to_vec()).collect()).rank()
}

fn parse_args(args: &[String]) -> Result<P8Config, String> {
    let mut config = P8Config {
        prime: 31,
        limit: 8,
        format: OutputFormat::Tsv,
    };
    let mut index = 0;
    while index < args.len() {
        let value = args
            .get(index + 1)
            .ok_or_else(|| format!("missing value for `{}`", args[index]))?;
        match args[index].as_str() {
            "--prime" => config.prime = parse_i64("--prime", value)?,
            "--limit" => config.limit = parse_usize("--limit", value)?,
            "--format" => config.format = parse_output_format(value)?,
            option => return Err(format!("unknown option `{option}`")),
        }
        index += 2;
    }

    if config.prime != 31 {
        return Err(format!(
            "unsupported prime {}; this smoke currently uses p=31",
            config.prime
        ));
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
        _ => Err(format!("invalid output format `{value}`; use tsv or jsonl")),
    }
}

fn usage() -> &'static str {
    "usage:
  search_p8 [--prime 31] [--limit N] [--format tsv|jsonl]"
}

#[cfg(test)]
mod tests {
    use super::*;

    fn args(values: &[&str]) -> Vec<String> {
        values.iter().map(|value| value.to_string()).collect()
    }

    #[test]
    fn parse_args_has_smoke_defaults() {
        assert_eq!(
            parse_args(&args(&[])).unwrap(),
            P8Config {
                prime: 31,
                limit: 8,
                format: OutputFormat::Tsv
            }
        );
    }

    #[test]
    fn parse_args_rejects_unsupported_prime_and_bad_format() {
        assert!(parse_args(&args(&["--prime", "41"])).is_err());
        assert!(parse_args(&args(&["--format", "xml"])).is_err());
        assert!(parse_args(&args(&["--limit", "0"])).is_err());
    }

    #[test]
    fn candidate_pool_is_nonempty() {
        assert!(!candidate_pool::<31>().is_empty());
    }
}
