use degree08::{
    Fp, PolynomialP3Fp,
    search_core::{
        ExperimentRecord, ProjectiveSurfaceScorerInput, SurfaceSymmetry, score_projective_surface,
    },
};

type Poly<const P: i64> = PolynomialP3Fp<P>;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Config {
    prime: i64,
    family: FamilySelection,
    grid_radius: i64,
    scan_limit: usize,
    limit: usize,
    format: OutputFormat,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum FamilySelection {
    All,
    QuadDet,
    CubicDisc,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum OutputFormat {
    Tsv,
    Json,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct ScoredRecord {
    label: String,
    score: isize,
    node_like: usize,
    bad_sing: usize,
    total_sing: usize,
    tsv: String,
    json: String,
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
        31 => print_records(run_for_prime::<31>(config), config.format),
        _ => unreachable!("unsupported prime was rejected by argument parsing"),
    }
    Ok(())
}

fn run_for_prime<const P: i64>(config: Config) -> Vec<ScoredRecord> {
    let tuples = parameter_tuples(config.grid_radius, config.scan_limit);
    let mut records = Vec::new();

    for model in config.family.models() {
        for (index, params) in tuples.iter().copied().enumerate() {
            let polynomial = model.polynomial::<P>(params);
            if polynomial.is_zero() || !polynomial.is_homogeneous() {
                continue;
            }

            let degree = polynomial.degree();
            let term_count = polynomial.terms().len();
            let input =
                ProjectiveSurfaceScorerInput::new(polynomial).with_symmetry(SurfaceSymmetry::None);
            let stats = score_projective_surface(&input);
            let score = stats.node_like() as isize - 8 * stats.bad_sing() as isize;
            let label = format!(
                "{}-{:03}-a{}-b{}-c{}-d{}",
                model.label(),
                index,
                params[0],
                params[1],
                params[2],
                params[3]
            );
            let record = ExperimentRecord::from_stats(
                format!("determinantal-{}", model.label()),
                label.clone(),
                score,
                &stats,
            )
            .with_tag("model", model.label())
            .with_tag("params", params_tag(params))
            .with_tag("degree", degree.to_string())
            .with_tag("terms", term_count.to_string())
            .with_tag("orbit_profile", orbit_profile_tag(stats.orbit_profile()))
            .with_tag("note", "finite-field-lift-candidate");

            records.push(ScoredRecord {
                label,
                score,
                node_like: stats.node_like(),
                bad_sing: stats.bad_sing(),
                total_sing: stats.total_sing(),
                tsv: record.to_tsv(),
                json: record.to_json_line(),
            });
        }
    }

    records.sort_by(|left, right| {
        right
            .score
            .cmp(&left.score)
            .then_with(|| right.node_like.cmp(&left.node_like))
            .then_with(|| left.bad_sing.cmp(&right.bad_sing))
            .then_with(|| right.total_sing.cmp(&left.total_sing))
            .then_with(|| left.label.cmp(&right.label))
    });
    records.truncate(config.limit);
    records
}

fn print_records(records: Vec<ScoredRecord>, format: OutputFormat) {
    match format {
        OutputFormat::Tsv => {
            println!("{}", ExperimentRecord::tsv_header());
            for record in records {
                println!("{}", record.tsv);
            }
        }
        OutputFormat::Json => {
            for record in records {
                println!("{}", record.json);
            }
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum DeterminantalModel {
    QuadDet,
    CubicDisc,
}

impl DeterminantalModel {
    fn label(self) -> &'static str {
        match self {
            Self::QuadDet => "quad-det",
            Self::CubicDisc => "cubic-disc",
        }
    }

    fn polynomial<const P: i64>(self, params: [i64; 4]) -> Poly<P> {
        match self {
            Self::QuadDet => quad_matrix_determinant(params),
            Self::CubicDisc => binary_cubic_discriminant(params),
        }
    }
}

impl FamilySelection {
    fn models(self) -> Vec<DeterminantalModel> {
        match self {
            Self::All => vec![DeterminantalModel::QuadDet, DeterminantalModel::CubicDisc],
            Self::QuadDet => vec![DeterminantalModel::QuadDet],
            Self::CubicDisc => vec![DeterminantalModel::CubicDisc],
        }
    }
}

fn quad_matrix_determinant<const P: i64>(params: [i64; 4]) -> Poly<P> {
    let [a, b, c, d] = params;
    let matrix = [
        [
            q::<P>(&[(1, [2, 0, 0, 0]), (a, [0, 1, 1, 0]), (d, [0, 0, 0, 2])]),
            q::<P>(&[(1, [1, 1, 0, 0]), (b, [0, 0, 1, 1])]),
            q::<P>(&[(1, [1, 0, 1, 0]), (c, [0, 1, 0, 1])]),
            q::<P>(&[(1, [1, 0, 0, 1]), (1, [0, 1, 1, 0])]),
        ],
        [
            q::<P>(&[(1, [1, 1, 0, 0]), (b, [0, 0, 1, 1])]),
            q::<P>(&[(1, [0, 2, 0, 0]), (a, [1, 0, 1, 0]), (d, [0, 0, 2, 0])]),
            q::<P>(&[(1, [0, 1, 1, 0]), (c, [1, 0, 0, 1])]),
            q::<P>(&[(1, [0, 1, 0, 1]), (1, [1, 0, 1, 0])]),
        ],
        [
            q::<P>(&[(1, [1, 0, 1, 0]), (c, [0, 1, 0, 1])]),
            q::<P>(&[(1, [0, 1, 1, 0]), (c, [1, 0, 0, 1])]),
            q::<P>(&[(1, [0, 0, 2, 0]), (a, [1, 0, 0, 1]), (d, [0, 2, 0, 0])]),
            q::<P>(&[(1, [0, 0, 1, 1]), (1, [1, 1, 0, 0])]),
        ],
        [
            q::<P>(&[(1, [1, 0, 0, 1]), (1, [0, 1, 1, 0])]),
            q::<P>(&[(1, [0, 1, 0, 1]), (1, [1, 0, 1, 0])]),
            q::<P>(&[(1, [0, 0, 1, 1]), (1, [1, 1, 0, 0])]),
            q::<P>(&[(1, [0, 0, 0, 2]), (a, [1, 1, 0, 0]), (d, [2, 0, 0, 0])]),
        ],
    ];
    det4(&matrix)
}

fn binary_cubic_discriminant<const P: i64>(params: [i64; 4]) -> Poly<P> {
    let [a, b, c, d] = params;
    let cubic_a = q::<P>(&[(1, [2, 0, 0, 0]), (a, [0, 1, 1, 0]), (b, [0, 0, 0, 2])]);
    let cubic_b = q::<P>(&[(1, [0, 2, 0, 0]), (b, [0, 0, 1, 1]), (c, [1, 0, 0, 1])]);
    let cubic_c = q::<P>(&[(1, [0, 0, 2, 0]), (c, [1, 1, 0, 0]), (d, [0, 1, 0, 1])]);
    let cubic_d = q::<P>(&[(1, [0, 0, 0, 2]), (d, [1, 0, 1, 0]), (a, [0, 1, 1, 0])]);

    // Discriminant of A s^3 + B s^2 t + C s t^2 + D t^3.
    let b2c2 = cubic_b.pow_usize(2).mul(&cubic_c.pow_usize(2));
    let ac3 = cubic_a.mul(&cubic_c.pow_usize(3)).scale(Fp::new(-4));
    let b3d = cubic_b.pow_usize(3).mul(&cubic_d).scale(Fp::new(-4));
    let a2d2 = cubic_a
        .pow_usize(2)
        .mul(&cubic_d.pow_usize(2))
        .scale(Fp::new(-27));
    let abcd = cubic_a
        .mul(&cubic_b)
        .mul(&cubic_c)
        .mul(&cubic_d)
        .scale(Fp::new(18));

    b2c2.add(&ac3).add(&b3d).add(&a2d2).add(&abcd)
}

fn det4<const P: i64>(matrix: &[[Poly<P>; 4]; 4]) -> Poly<P> {
    let mut determinant = Poly::<P>::zero();
    for permutation in permutations4() {
        let term = (0..4).fold(
            Poly::<P>::constant(Fp::new(permutation_sign(permutation))),
            |product, row| product.mul(&matrix[row][permutation[row]]),
        );
        determinant = determinant.add(&term);
    }
    determinant
}

fn q<const P: i64>(terms: &[(i64, [usize; 4])]) -> Poly<P> {
    Poly::<P>::from_terms(
        terms
            .iter()
            .map(|(coefficient, exponents)| (Fp::new(*coefficient), *exponents))
            .collect(),
    )
}

fn permutations4() -> [[usize; 4]; 24] {
    [
        [0, 1, 2, 3],
        [0, 1, 3, 2],
        [0, 2, 1, 3],
        [0, 2, 3, 1],
        [0, 3, 1, 2],
        [0, 3, 2, 1],
        [1, 0, 2, 3],
        [1, 0, 3, 2],
        [1, 2, 0, 3],
        [1, 2, 3, 0],
        [1, 3, 0, 2],
        [1, 3, 2, 0],
        [2, 0, 1, 3],
        [2, 0, 3, 1],
        [2, 1, 0, 3],
        [2, 1, 3, 0],
        [2, 3, 0, 1],
        [2, 3, 1, 0],
        [3, 0, 1, 2],
        [3, 0, 2, 1],
        [3, 1, 0, 2],
        [3, 1, 2, 0],
        [3, 2, 0, 1],
        [3, 2, 1, 0],
    ]
}

fn permutation_sign(permutation: [usize; 4]) -> i64 {
    let inversions = (0..4)
        .flat_map(|left| ((left + 1)..4).map(move |right| (left, right)))
        .filter(|(left, right)| permutation[*left] > permutation[*right])
        .count();
    if inversions % 2 == 0 { 1 } else { -1 }
}

fn parameter_tuples(radius: i64, limit: usize) -> Vec<[i64; 4]> {
    let values = (-radius..=radius).collect::<Vec<_>>();
    let mut tuples = Vec::new();
    for &a in &values {
        for &b in &values {
            for &c in &values {
                for &d in &values {
                    tuples.push([a, b, c, d]);
                    if tuples.len() == limit {
                        return tuples;
                    }
                }
            }
        }
    }
    tuples
}

fn orbit_profile_tag(profile: &std::collections::BTreeMap<usize, usize>) -> String {
    if profile.is_empty() {
        return "empty".to_string();
    }
    profile
        .iter()
        .map(|(orbit_size, count)| format!("{orbit_size}:{count}"))
        .collect::<Vec<_>>()
        .join(",")
}

fn params_tag(params: [i64; 4]) -> String {
    format!("{},{},{},{}", params[0], params[1], params[2], params[3])
}

fn parse_args(args: &[String]) -> Result<Config, String> {
    if matches!(
        args.first().map(String::as_str),
        Some("-h" | "--help" | "help")
    ) {
        println!("{}", usage());
        std::process::exit(0);
    }

    let mut config = Config {
        prime: 31,
        family: FamilySelection::All,
        grid_radius: 1,
        scan_limit: 24,
        limit: 10,
        format: OutputFormat::Tsv,
    };

    let mut index = 0;
    while index < args.len() {
        let value = args
            .get(index + 1)
            .ok_or_else(|| format!("missing value for `{}`", args[index]))?;
        match args[index].as_str() {
            "--prime" => config.prime = parse_i64("--prime", value)?,
            "--family" => config.family = parse_family(value)?,
            "--grid-radius" => config.grid_radius = parse_i64("--grid-radius", value)?,
            "--scan-limit" => config.scan_limit = parse_usize("--scan-limit", value)?,
            "--limit" => config.limit = parse_usize("--limit", value)?,
            "--format" => config.format = parse_output_format(value)?,
            option => return Err(format!("unknown option `{option}`")),
        }
        index += 2;
    }

    validate_config(config)?;
    Ok(config)
}

fn validate_config(config: Config) -> Result<(), String> {
    if config.prime != 31 {
        return Err(format!(
            "unsupported prime {}; this prototype currently uses p=31",
            config.prime
        ));
    }
    if config.grid_radius < 0 {
        return Err("--grid-radius must be non-negative".to_string());
    }
    if config.scan_limit == 0 {
        return Err("--scan-limit must be positive".to_string());
    }
    if config.limit == 0 {
        return Err("--limit must be positive".to_string());
    }
    Ok(())
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

fn parse_family(value: &str) -> Result<FamilySelection, String> {
    match value {
        "all" => Ok(FamilySelection::All),
        "quad-det" | "det" => Ok(FamilySelection::QuadDet),
        "cubic-disc" | "disc" => Ok(FamilySelection::CubicDisc),
        _ => Err(format!(
            "invalid family `{value}`; use all, quad-det, or cubic-disc"
        )),
    }
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
  search_determinantal [--prime 31] [--family all|quad-det|cubic-disc] [--grid-radius N] [--scan-limit N] [--limit N] [--format tsv|json]

This is a finite-field prototype for determinantal/discriminant octic families.
It scans a small parameter grid over F_31 and reports unified ExperimentRecord rows."
}
