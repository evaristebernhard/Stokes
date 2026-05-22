use degree08::{
    Fp,
    critical_profile::{
        AffineLineArrangementFp, AffineLineArrangementQuality, AffineLineFp, CriticalValueProfile,
        WeightedCriticalPair, affine_line_arrangement_quality, chebyshev_profile_surface,
        critical_value_profile_for_lines_fast, line_product_polynomial, slope_polynomial_lines,
    },
    search_core::{ExperimentRecord, ProjectiveSurfaceScorerInput, score_projective_surface},
};
use nodal_core::FieldElement;
use std::cmp::Ordering;
use std::collections::BinaryHeap;

#[derive(Clone, Debug, Eq, PartialEq)]
struct Config {
    prime: i64,
    family: Family,
    coefficient_count: usize,
    sample_mode: SampleMode,
    seed: u64,
    grid_radius: i64,
    scan_limit: usize,
    profile_limit: usize,
    verify_top: usize,
    directions: usize,
    intercepts_per_direction: usize,
    local_climb: usize,
    pair_sweep: usize,
    fixed_params: Option<Vec<i64>>,
    format: OutputFormat,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Family {
    SlopePoly,
    Normal10,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum SampleMode {
    Shell,
    Lcg,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum OutputFormat {
    Tsv,
    Json,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct ProfileCandidate<const P: i64> {
    label: String,
    params: Vec<i64>,
    lines: Vec<AffineLineFp<P>>,
    profile: CriticalValueProfile<P>,
    pair: WeightedCriticalPair<P>,
    zero_morse: usize,
    best_nonzero_morse: usize,
    quality: AffineLineArrangementQuality,
    sample_mode: SampleMode,
    seed: u64,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct CandidateKey {
    predicted_nodes: usize,
    zero_morse: usize,
    best_nonzero_morse: usize,
    selected_degenerate: usize,
    degenerate_critical: usize,
}

impl Ord for CandidateKey {
    fn cmp(&self, other: &Self) -> Ordering {
        self.predicted_nodes
            .cmp(&other.predicted_nodes)
            .then_with(|| self.zero_morse.cmp(&other.zero_morse))
            .then_with(|| self.best_nonzero_morse.cmp(&other.best_nonzero_morse))
            .then_with(|| other.selected_degenerate.cmp(&self.selected_degenerate))
            .then_with(|| other.degenerate_critical.cmp(&self.degenerate_critical))
    }
}

impl PartialOrd for CandidateKey {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

struct HeapEntry<const P: i64> {
    key: CandidateKey,
    sequence: usize,
    candidate: ProfileCandidate<P>,
}

impl<const P: i64> Eq for HeapEntry<P> {}

impl<const P: i64> PartialEq for HeapEntry<P> {
    fn eq(&self, other: &Self) -> bool {
        self.key == other.key && self.sequence == other.sequence
    }
}

impl<const P: i64> Ord for HeapEntry<P> {
    fn cmp(&self, other: &Self) -> Ordering {
        other
            .key
            .cmp(&self.key)
            .then_with(|| other.sequence.cmp(&self.sequence))
    }
}

impl<const P: i64> PartialOrd for HeapEntry<P> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

struct TopCandidateHeap<const P: i64> {
    limit: usize,
    next_sequence: usize,
    heap: BinaryHeap<HeapEntry<P>>,
}

impl<const P: i64> TopCandidateHeap<P> {
    fn new(limit: usize) -> Self {
        Self {
            limit,
            next_sequence: 0,
            heap: BinaryHeap::new(),
        }
    }

    fn push(&mut self, candidate: ProfileCandidate<P>) {
        let key = candidate_key(&candidate);
        let entry = HeapEntry {
            key,
            sequence: self.next_sequence,
            candidate,
        };
        self.next_sequence += 1;

        if self.heap.len() < self.limit {
            self.heap.push(entry);
            return;
        }

        if self
            .heap
            .peek()
            .map(|worst| entry.key > worst.key)
            .unwrap_or(true)
        {
            self.heap.pop();
            self.heap.push(entry);
        }
    }

    fn extend<I>(&mut self, candidates: I)
    where
        I: IntoIterator<Item = ProfileCandidate<P>>,
    {
        for candidate in candidates {
            self.push(candidate);
        }
    }

    fn sorted_candidates(&self) -> Vec<ProfileCandidate<P>> {
        let mut candidates = self
            .heap
            .iter()
            .map(|entry| entry.candidate.clone())
            .collect::<Vec<_>>();
        sort_candidates(&mut candidates);
        candidates
    }

    fn into_sorted_candidates(self) -> Vec<ProfileCandidate<P>> {
        let mut candidates = self
            .heap
            .into_iter()
            .map(|entry| entry.candidate)
            .collect::<Vec<_>>();
        sort_candidates(&mut candidates);
        candidates
    }
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
        31 => print_records(run_for_prime::<31>(&config), config.format),
        47 => print_records(run_for_prime::<47>(&config), config.format),
        97 => print_records(run_for_prime::<97>(&config), config.format),
        113 => print_records(run_for_prime::<113>(&config), config.format),
        127 => print_records(run_for_prime::<127>(&config), config.format),
        _ => unreachable!("unsupported prime was rejected by argument parsing"),
    }
    Ok(())
}

fn run_for_prime<const P: i64>(config: &Config) -> Vec<ExperimentRecord> {
    scan_profiles::<P>(config)
        .into_iter()
        .take(config.verify_top)
        .map(|candidate| verify_candidate(config.family, candidate))
        .collect()
}

fn scan_profiles<const P: i64>(config: &Config) -> Vec<ProfileCandidate<P>> {
    let mut heap = TopCandidateHeap::new(config.profile_limit);

    if let Some(params) = config.fixed_params.clone() {
        if let Some(candidate) = candidate_from_params::<P>(config, params, 0, "fixed") {
            heap.push(candidate);
        }
        return heap.into_sorted_candidates();
    }

    match config.family {
        Family::SlopePoly => {
            for (index, params) in parameter_tuples::<P>(
                config.coefficient_count,
                config.grid_radius,
                config.scan_limit,
                config.sample_mode,
                config.seed,
            )
            .into_iter()
            .enumerate()
            {
                if let Some(candidate) = candidate_from_params::<P>(config, params, index, "scan") {
                    heap.push(candidate);
                }
            }
        }
        Family::Normal10 => {
            let mut lcg = Lcg::new(config.seed);
            let mut index = 0;
            'directions: for _ in 0..config.directions {
                let directions = (0..5).map(|_| lcg.next_centered::<P>()).collect::<Vec<_>>();
                for _ in 0..config.intercepts_per_direction {
                    if index >= config.scan_limit {
                        break 'directions;
                    }
                    let mut params = directions.clone();
                    params.extend((0..5).map(|_| lcg.next_nonzero_centered::<P>()));
                    if let Some(candidate) =
                        candidate_from_params::<P>(config, params, index, "layered")
                    {
                        heap.push(candidate);
                    }
                    index += 1;
                }
            }
        }
    }

    let climb_seeds = heap
        .sorted_candidates()
        .into_iter()
        .take(config.local_climb)
        .collect::<Vec<_>>();
    let climbed = climb_seeds
        .iter()
        .filter_map(|candidate| coordinate_climb(config, candidate))
        .collect::<Vec<_>>();
    heap.extend(climbed);

    let sweep_seeds = heap
        .sorted_candidates()
        .into_iter()
        .take(config.pair_sweep)
        .collect::<Vec<_>>();
    let swept = sweep_seeds
        .iter()
        .filter_map(|candidate| pair_sweep(config, candidate))
        .collect::<Vec<_>>();
    heap.extend(swept);

    heap.into_sorted_candidates()
}

fn candidate_from_params<const P: i64>(
    config: &Config,
    params: Vec<i64>,
    index: usize,
    stage: &str,
) -> Option<ProfileCandidate<P>> {
    let lines = lines_for_params::<P>(config.family, config.coefficient_count, &params)?;
    let quality = affine_line_arrangement_quality(&lines);
    if !quality.simple() {
        return None;
    }

    let profile = critical_value_profile_for_lines_fast(&lines);
    let pair = profile.best_weighted_pairs(1).into_iter().next()?;
    let zero_morse = profile
        .bucket(Fp::zero())
        .map(|bucket| bucket.morse_count())
        .unwrap_or(0);
    let best_nonzero_morse = profile
        .buckets()
        .values()
        .filter(|bucket| bucket.value() != Fp::zero())
        .map(|bucket| bucket.morse_count())
        .max()
        .unwrap_or(0);

    Some(ProfileCandidate {
        label: format!("{}-{}-{:06}", config.family.label(), stage, index),
        params,
        lines,
        profile,
        pair,
        zero_morse,
        best_nonzero_morse,
        quality,
        sample_mode: config.sample_mode,
        seed: config.seed,
    })
}

fn lines_for_params<const P: i64>(
    family: Family,
    coefficient_count: usize,
    params: &[i64],
) -> Option<Vec<AffineLineFp<P>>> {
    match family {
        Family::SlopePoly => Some(slope_polynomial_lines::<P>(&params[..coefficient_count])),
        Family::Normal10 => AffineLineArrangementFp::<P>::normal_form10_from_slice(params)
            .ok()
            .map(|arrangement| arrangement.lines().to_vec()),
    }
}

fn coordinate_climb<const P: i64>(
    config: &Config,
    start: &ProfileCandidate<P>,
) -> Option<ProfileCandidate<P>> {
    let mut best = start.clone();
    let mut improved = false;
    let parameter_count = config.family.parameter_count(config.coefficient_count);

    for coordinate in 0..parameter_count {
        let mut coordinate_best = best.clone();
        for residue in 0..P {
            let mut params = best.params.clone();
            params[coordinate] = residue_to_centered::<P>(residue);
            if let Some(mut candidate) = candidate_from_params::<P>(
                config,
                params,
                coordinate * P as usize + residue as usize,
                "climb",
            ) {
                candidate.label = format!("{}-climb-c{}", start.label, coordinate);
                if candidate_key(&candidate) > candidate_key(&coordinate_best) {
                    coordinate_best = candidate;
                }
            }
        }
        if candidate_key(&coordinate_best) > candidate_key(&best) {
            best = coordinate_best;
            improved = true;
        }
    }

    improved.then_some(best)
}

fn pair_sweep<const P: i64>(
    config: &Config,
    start: &ProfileCandidate<P>,
) -> Option<ProfileCandidate<P>> {
    let mut best = start.clone();
    let mut improved = false;
    let parameter_count = config.family.parameter_count(config.coefficient_count);

    for first in 0..parameter_count {
        for second in (first + 1)..parameter_count {
            let mut pair_best = best.clone();
            for first_residue in 0..P {
                for second_residue in 0..P {
                    let mut params = best.params.clone();
                    params[first] = residue_to_centered::<P>(first_residue);
                    params[second] = residue_to_centered::<P>(second_residue);
                    let index = (((first * parameter_count + second) as i64 * P + first_residue)
                        * P
                        + second_residue) as usize;
                    if let Some(mut candidate) =
                        candidate_from_params::<P>(config, params, index, "pair")
                    {
                        candidate.label = format!("{}-pair-c{}-{}", start.label, first, second);
                        if candidate_key(&candidate) > candidate_key(&pair_best) {
                            pair_best = candidate;
                        }
                    }
                }
            }
            if candidate_key(&pair_best) > candidate_key(&best) {
                best = pair_best;
                improved = true;
            }
        }
    }

    improved.then_some(best)
}

fn verify_candidate<const P: i64>(
    family: Family,
    candidate: ProfileCandidate<P>,
) -> ExperimentRecord {
    let polynomial = line_product_polynomial(&candidate.lines);
    let surface = chebyshev_profile_surface(&polynomial, candidate.pair);
    let stats = score_projective_surface(&ProjectiveSurfaceScorerInput::new(surface));
    let score = stats.node_like() as isize - 8 * stats.bad_sing() as isize;

    ExperimentRecord::from_stats(
        "critical-profile-eight-line",
        candidate.label,
        score,
        &stats,
    )
    .with_tag("route", "critical-value-profile")
    .with_tag("family", family.label())
    .with_tag("sample", candidate.sample_mode.label())
    .with_tag("seed", candidate.seed.to_string())
    .with_tag("params", params_tag(&candidate.params))
    .with_tag("model", "alpha*Q_h(x,y,w)+T8_h(z,w)+lambda*w^8")
    .with_tag(
        "alpha",
        candidate.pair.chebyshev_scale().value().to_string(),
    )
    .with_tag(
        "lambda",
        candidate.pair.chebyshev_lambda().value().to_string(),
    )
    .with_tag(
        "primary_value",
        candidate.pair.primary_value().value().to_string(),
    )
    .with_tag(
        "secondary_value",
        candidate.pair.secondary_value().value().to_string(),
    )
    .with_tag("primary_morse", candidate.pair.primary_morse().to_string())
    .with_tag(
        "secondary_morse",
        candidate.pair.secondary_morse().to_string(),
    )
    .with_tag(
        "predicted_affine_nodes",
        candidate.pair.predicted_nodes().to_string(),
    )
    .with_tag(
        "selected_degenerate",
        candidate.pair.selected_degenerate().to_string(),
    )
    .with_tag("zero_morse", candidate.zero_morse.to_string())
    .with_tag(
        "best_nonzero_morse",
        candidate.best_nonzero_morse.to_string(),
    )
    .with_tag(
        "total_critical_visible",
        candidate.profile.total_critical().to_string(),
    )
    .with_tag(
        "morse_critical_visible",
        candidate.profile.morse_critical().to_string(),
    )
    .with_tag(
        "degenerate_critical_visible",
        candidate.profile.degenerate_critical().to_string(),
    )
    .with_tag("profile", candidate.profile.signature(8))
    .with_tag("quality_pairs", candidate.quality.pair_count().to_string())
    .with_tag(
        "quality_triples",
        candidate.quality.triple_count().to_string(),
    )
    .with_tag(
        "parallel_pairs",
        candidate.quality.parallel_pair_count().to_string(),
    )
    .with_tag(
        "concurrent_triples",
        candidate.quality.concurrent_triple_count().to_string(),
    )
    .with_tag(
        "infinity_degenerate_lines",
        candidate
            .quality
            .infinity_degenerate_line_count()
            .to_string(),
    )
    .with_tag("orbit_profile", format_orbit_profile(stats.orbit_profile()))
}

fn parameter_tuples<const P: i64>(
    count: usize,
    radius: i64,
    limit: usize,
    sample_mode: SampleMode,
    seed: u64,
) -> Vec<Vec<i64>> {
    match sample_mode {
        SampleMode::Shell => shell_parameter_tuples(count, radius, limit),
        SampleMode::Lcg => lcg_parameter_tuples::<P>(count, limit, seed),
    }
}

fn shell_parameter_tuples(count: usize, radius: i64, limit: usize) -> Vec<Vec<i64>> {
    let mut tuples = Vec::new();
    for shell in 0..=radius {
        let values = (-shell..=shell).collect::<Vec<_>>();
        let mut current = Vec::with_capacity(count);
        enumerate_parameter_tuples(count, shell, &values, limit, &mut current, &mut tuples);
        if tuples.len() >= limit {
            break;
        }
    }
    tuples
}

fn lcg_parameter_tuples<const P: i64>(count: usize, limit: usize, seed: u64) -> Vec<Vec<i64>> {
    let mut tuples = Vec::new();
    let mut lcg = Lcg::new(seed);
    while tuples.len() < limit {
        let tuple = (0..count)
            .map(|_| lcg.next_centered::<P>())
            .collect::<Vec<_>>();
        if tuple.iter().any(|value| *value != 0) {
            tuples.push(tuple);
        }
    }
    tuples
}

fn enumerate_parameter_tuples(
    count: usize,
    shell: i64,
    values: &[i64],
    limit: usize,
    current: &mut Vec<i64>,
    output: &mut Vec<Vec<i64>>,
) {
    if output.len() >= limit {
        return;
    }
    if current.len() == count {
        let max_abs = current.iter().map(|value| value.abs()).max().unwrap_or(0);
        if max_abs == shell && max_abs != 0 {
            output.push(current.clone());
        }
        return;
    }

    for &value in values {
        current.push(value);
        enumerate_parameter_tuples(count, shell, values, limit, current, output);
        current.pop();
        if output.len() >= limit {
            return;
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Lcg {
    state: u64,
}

impl Lcg {
    fn new(seed: u64) -> Self {
        Self { state: seed.max(1) }
    }

    fn next_residue<const P: i64>(&mut self) -> i64 {
        self.state = self
            .state
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        (self.state % P as u64) as i64
    }

    fn next_centered<const P: i64>(&mut self) -> i64 {
        residue_to_centered::<P>(self.next_residue::<P>())
    }

    fn next_nonzero_centered<const P: i64>(&mut self) -> i64 {
        loop {
            let value = self.next_centered::<P>();
            if value != 0 {
                return value;
            }
        }
    }
}

fn residue_to_centered<const P: i64>(residue: i64) -> i64 {
    if residue > P / 2 {
        residue - P
    } else {
        residue
    }
}

fn candidate_key<const P: i64>(candidate: &ProfileCandidate<P>) -> CandidateKey {
    CandidateKey {
        predicted_nodes: candidate.pair.predicted_nodes(),
        zero_morse: candidate.zero_morse,
        best_nonzero_morse: candidate.best_nonzero_morse,
        selected_degenerate: candidate.pair.selected_degenerate(),
        degenerate_critical: candidate.profile.degenerate_critical(),
    }
}

fn sort_candidates<const P: i64>(candidates: &mut [ProfileCandidate<P>]) {
    candidates.sort_by(|left, right| {
        candidate_key(right)
            .cmp(&candidate_key(left))
            .then_with(|| left.label.cmp(&right.label))
    });
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

fn params_tag(params: &[i64]) -> String {
    params
        .iter()
        .map(i64::to_string)
        .collect::<Vec<_>>()
        .join(",")
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

fn parse_args(args: &[String]) -> Result<Config, String> {
    let mut config = Config {
        prime: 31,
        family: Family::SlopePoly,
        coefficient_count: 6,
        sample_mode: SampleMode::Lcg,
        seed: 1,
        grid_radius: 2,
        scan_limit: 20_000,
        profile_limit: 32,
        verify_top: 8,
        directions: 256,
        intercepts_per_direction: 256,
        local_climb: 0,
        pair_sweep: 0,
        fixed_params: None,
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
            "--coeff-count" => config.coefficient_count = parse_usize("--coeff-count", value)?,
            "--sample" => config.sample_mode = parse_sample_mode(value)?,
            "--seed" => config.seed = parse_u64("--seed", value)?,
            "--grid-radius" => config.grid_radius = parse_i64("--grid-radius", value)?,
            "--scan-limit" => config.scan_limit = parse_usize("--scan-limit", value)?,
            "--profile-limit" => config.profile_limit = parse_usize("--profile-limit", value)?,
            "--verify-top" => config.verify_top = parse_usize("--verify-top", value)?,
            "--directions" => config.directions = parse_usize("--directions", value)?,
            "--intercepts" | "--intercepts-per-direction" => {
                config.intercepts_per_direction = parse_usize("--intercepts-per-direction", value)?;
            }
            "--local-climb" => config.local_climb = parse_usize("--local-climb", value)?,
            "--pair-sweep" => config.pair_sweep = parse_usize("--pair-sweep", value)?,
            "--params" => config.fixed_params = Some(parse_params(value)?),
            "--format" => config.format = parse_output_format(value)?,
            option => return Err(format!("unknown option `{option}`")),
        }
        index += 2;
    }

    validate_config(config)
}

fn validate_config(config: Config) -> Result<Config, String> {
    if !matches!(config.prime, 31 | 47 | 97 | 113 | 127) {
        return Err(format!(
            "unsupported prime {}; use one of 31,47,97,113,127",
            config.prime
        ));
    }
    if config.coefficient_count == 0 || config.coefficient_count > 6 {
        return Err("--coeff-count must lie in 1..=6".to_string());
    }
    if config.grid_radius < 1 {
        return Err("--grid-radius must be positive".to_string());
    }
    if config.scan_limit == 0 {
        return Err("--scan-limit must be positive".to_string());
    }
    if config.profile_limit == 0 {
        return Err("--profile-limit must be positive".to_string());
    }
    if config.verify_top == 0 {
        return Err("--verify-top must be positive".to_string());
    }
    if config.directions == 0 {
        return Err("--directions must be positive".to_string());
    }
    if config.intercepts_per_direction == 0 {
        return Err("--intercepts-per-direction must be positive".to_string());
    }
    if let Some(params) = config.fixed_params.as_ref() {
        let expected = config.family.parameter_count(config.coefficient_count);
        if params.len() != expected {
            return Err(format!(
                "--params for {} expects exactly {} values: got {}",
                config.family.label(),
                expected,
                params.len()
            ));
        }
    }
    Ok(config)
}

impl Family {
    fn label(self) -> &'static str {
        match self {
            Self::SlopePoly => "slope-poly",
            Self::Normal10 => "normal10",
        }
    }

    fn parameter_count(self, coefficient_count: usize) -> usize {
        match self {
            Self::SlopePoly => coefficient_count,
            Self::Normal10 => 10,
        }
    }
}

impl SampleMode {
    fn label(self) -> &'static str {
        match self {
            Self::Shell => "shell",
            Self::Lcg => "lcg",
        }
    }
}

fn parse_family(value: &str) -> Result<Family, String> {
    match value {
        "slope-poly" | "slope_polynomial" => Ok(Family::SlopePoly),
        "normal10" | "normal-10" | "normal_form10" => Ok(Family::Normal10),
        _ => Err(format!(
            "invalid family `{value}`; supported: slope-poly, normal10"
        )),
    }
}

fn parse_sample_mode(value: &str) -> Result<SampleMode, String> {
    match value {
        "shell" => Ok(SampleMode::Shell),
        "lcg" | "random" | "full" | "layered" => Ok(SampleMode::Lcg),
        _ => Err(format!("invalid sample mode `{value}`; use shell or lcg")),
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

fn parse_u64(name: &str, value: &str) -> Result<u64, String> {
    value
        .parse()
        .map_err(|_| format!("invalid unsigned integer for `{name}`: `{value}`"))
}

fn parse_output_format(value: &str) -> Result<OutputFormat, String> {
    match value {
        "tsv" => Ok(OutputFormat::Tsv),
        "json" | "jsonl" => Ok(OutputFormat::Json),
        _ => Err(format!("invalid output format `{value}`; use tsv or json")),
    }
}

fn parse_params(value: &str) -> Result<Vec<i64>, String> {
    value
        .split(',')
        .filter(|entry| !entry.trim().is_empty())
        .map(|entry| {
            entry
                .trim()
                .parse::<i64>()
                .map_err(|_| format!("invalid parameter `{entry}`"))
        })
        .collect()
}

fn usage() -> &'static str {
    "usage:
  search_critical_profile [--prime 31|47|97|113|127]
    [--family slope-poly|normal10] [--coeff-count N] [--sample shell|lcg]
    [--seed N] [--grid-radius N] [--scan-limit N]
    [--directions N] [--intercepts-per-direction N]
    [--local-climb N] [--pair-sweep N]
    [--params comma,separated,values]
    [--profile-limit N] [--verify-top N]
    [--format tsv|json]

Families:
  slope-poly: l_t = x + t*y + (a0*t^2 + a1*t^3 + ...), t in {-4,-3,-2,-1,1,2,3,4}.
  normal10:   L0=x, L1=y, L2=1-x-y, Li=1+s_i(r_i*x+y), i=3..7.

For each simple arrangement the scanner ranks the finite-field critical-value
profile of Q=prod_i L_i using a direct line-value fast path, then verifies top
hits by scoring alpha*Q_h(x,y,w)+T8_h(z,w)+lambda*w^8 as a projective octic."
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parse_args_has_checked_defaults() {
        let config = parse_args(&[]).unwrap();

        assert_eq!(config.prime, 31);
        assert_eq!(config.family, Family::SlopePoly);
        assert_eq!(config.coefficient_count, 6);
        assert_eq!(config.sample_mode, SampleMode::Lcg);
        assert_eq!(config.scan_limit, 20_000);
        assert_eq!(config.profile_limit, 32);
        assert_eq!(config.verify_top, 8);
        assert_eq!(config.directions, 256);
        assert_eq!(config.intercepts_per_direction, 256);
        assert_eq!(config.fixed_params, None);
    }

    #[test]
    fn parse_args_accepts_normal10_sampling_controls_and_json() {
        let args = [
            "--prime",
            "47",
            "--family",
            "normal10",
            "--directions",
            "7",
            "--intercepts",
            "11",
            "--local-climb",
            "2",
            "--pair-sweep",
            "1",
            "--format",
            "json",
        ]
        .map(String::from);
        let config = parse_args(&args).unwrap();

        assert_eq!(config.prime, 47);
        assert_eq!(config.family, Family::Normal10);
        assert_eq!(config.directions, 7);
        assert_eq!(config.intercepts_per_direction, 11);
        assert_eq!(config.local_climb, 2);
        assert_eq!(config.pair_sweep, 1);
        assert_eq!(config.format, OutputFormat::Json);
    }

    #[test]
    fn parse_args_rejects_unsupported_prime_and_bad_counts() {
        assert!(parse_args(&["--prime".to_string(), "41".to_string()]).is_err());
        assert!(parse_args(&["--coeff-count".to_string(), "0".to_string()]).is_err());
        assert!(parse_args(&["--profile-limit".to_string(), "0".to_string()]).is_err());
        assert!(parse_args(&["--directions".to_string(), "0".to_string()]).is_err());
        assert!(
            parse_args(&["--family", "normal10", "--params", "1,2,3"].map(String::from),).is_err()
        );
    }

    #[test]
    fn normal10_candidate_uses_fast_line_profile() {
        let config = parse_args(
            &[
                "--family",
                "normal10",
                "--scan-limit",
                "1",
                "--verify-top",
                "1",
            ]
            .map(String::from),
        )
        .unwrap();
        let candidate = candidate_from_params::<31>(
            &config,
            vec![3, 13, -8, 11, -13, 13, -11, 5, -3, 6],
            0,
            "test",
        )
        .unwrap();

        assert_eq!(candidate.lines.len(), 8);
        assert_eq!(candidate.zero_morse, 28);
        assert!(candidate.pair.predicted_nodes() >= 112);
    }
}
