use super::{
    BaseLineLengthCheck, BaseLineLengthStats, FiniteFieldSingularPoint,
    FiniteFieldSingularityStats, Fp, PolynomialP3Fp,
};
use nodal_core::{FieldElement, Matrix, P3_VARIABLE_COUNT};
use std::collections::{BTreeMap, BTreeSet, VecDeque};

pub type ProjectivePointFp<const P: i64> = [Fp<P>; P3_VARIABLE_COUNT];
pub type ProjectivePlanePointFp<const P: i64> = [Fp<P>; 3];
pub type ProjectiveLinePointFp<const P: i64> = [Fp<P>; 2];
pub type PlaneFp<const P: i64> = [Fp<P>; P3_VARIABLE_COUNT];
pub type SurfacePolynomialFp<const P: i64> = PolynomialP3Fp<P>;

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ProjectiveLinearMap<const P: i64> {
    matrix: [[Fp<P>; P3_VARIABLE_COUNT]; P3_VARIABLE_COUNT],
}

impl<const P: i64> ProjectiveLinearMap<P> {
    pub fn new(matrix: [[Fp<P>; P3_VARIABLE_COUNT]; P3_VARIABLE_COUNT]) -> Self {
        Self { matrix }
    }

    pub fn apply(&self, point: &ProjectivePointFp<P>) -> ProjectivePointFp<P> {
        std::array::from_fn(|row| {
            self.matrix[row]
                .iter()
                .zip(point)
                .fold(Fp::zero(), |sum, (coefficient, coord)| {
                    sum + *coefficient * *coord
                })
        })
    }
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub enum SurfaceSymmetry<const P: i64> {
    #[default]
    None,
    D4TimesZ2,
    D8TimesZ2 {
        sqrt2: Fp<P>,
    },
    Explicit(Vec<ProjectiveLinearMap<P>>),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PlaneProductSkeleton<const P: i64> {
    planes: Vec<PlaneFp<P>>,
    quartic_r: SurfacePolynomialFp<P>,
}

impl<const P: i64> PlaneProductSkeleton<P> {
    pub fn new(planes: Vec<PlaneFp<P>>, quartic_r: SurfacePolynomialFp<P>) -> Self {
        Self { planes, quartic_r }
    }

    pub fn planes(&self) -> &[PlaneFp<P>] {
        &self.planes
    }

    pub fn quartic_r(&self) -> &SurfacePolynomialFp<P> {
        &self.quartic_r
    }

    pub fn plane_product(&self, scale: Fp<P>) -> SurfacePolynomialFp<P> {
        self.planes.iter().copied().map(linear_form).fold(
            SurfacePolynomialFp::<P>::constant(scale),
            |product, factor| product.mul(&factor),
        )
    }

    pub fn p8_minus_r4_squared(&self, scale: Fp<P>) -> SurfacePolynomialFp<P> {
        self.plane_product(scale).sub(&self.quartic_r.pow_usize(2))
    }

    pub fn base_line_length_stats(&self) -> BaseLineLengthStats {
        score_plane_product_base_lines(self)
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ProjectiveSurfaceScorerInput<const P: i64> {
    polynomial: SurfacePolynomialFp<P>,
    plane_product_skeleton: Option<PlaneProductSkeleton<P>>,
    symmetry: SurfaceSymmetry<P>,
}

impl<const P: i64> ProjectiveSurfaceScorerInput<P> {
    pub fn new(polynomial: SurfacePolynomialFp<P>) -> Self {
        Self {
            polynomial,
            plane_product_skeleton: None,
            symmetry: SurfaceSymmetry::None,
        }
    }

    pub fn with_plane_product_skeleton(mut self, skeleton: PlaneProductSkeleton<P>) -> Self {
        self.plane_product_skeleton = Some(skeleton);
        self
    }

    pub fn with_symmetry(mut self, symmetry: SurfaceSymmetry<P>) -> Self {
        self.symmetry = symmetry;
        self
    }

    pub fn polynomial(&self) -> &SurfacePolynomialFp<P> {
        &self.polynomial
    }

    pub fn plane_product_skeleton(&self) -> Option<&PlaneProductSkeleton<P>> {
        self.plane_product_skeleton.as_ref()
    }

    pub fn symmetry(&self) -> &SurfaceSymmetry<P> {
        &self.symmetry
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ExperimentRecord {
    family: String,
    prime: i64,
    label: String,
    total_sing: usize,
    node_like: usize,
    bad_sing: usize,
    base_like: usize,
    extra_like: usize,
    score: isize,
    tags: Vec<(String, String)>,
}

impl ExperimentRecord {
    pub fn from_stats<const P: i64>(
        family: impl Into<String>,
        label: impl Into<String>,
        score: isize,
        stats: &FiniteFieldSingularityStats<P>,
    ) -> Self {
        Self {
            family: family.into(),
            prime: P,
            label: label.into(),
            total_sing: stats.total_sing(),
            node_like: stats.node_like(),
            bad_sing: stats.bad_sing(),
            base_like: stats.base_like(),
            extra_like: stats.extra_like(),
            score,
            tags: Vec::new(),
        }
    }

    pub fn with_tag(mut self, key: impl Into<String>, value: impl Into<String>) -> Self {
        self.tags.push((key.into(), value.into()));
        self
    }

    pub fn tsv_header() -> &'static str {
        "family\tprime\tlabel\ttotal_sing\tnode_like\tbad_sing\tbase_like\textra_like\tscore\ttags"
    }

    pub fn to_tsv(&self) -> String {
        format!(
            "{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}",
            self.family,
            self.prime,
            self.label,
            self.total_sing,
            self.node_like,
            self.bad_sing,
            self.base_like,
            self.extra_like,
            self.score,
            self.tags_tsv()
        )
    }

    pub fn to_json_line(&self) -> String {
        let tags = self
            .tags
            .iter()
            .map(|(key, value)| {
                format!(
                    "\"{}\":\"{}\"",
                    escape_json(key.as_str()),
                    escape_json(value.as_str())
                )
            })
            .collect::<Vec<_>>()
            .join(",");
        format!(
            "{{\"family\":\"{}\",\"prime\":{},\"label\":\"{}\",\"total_sing\":{},\"node_like\":{},\"bad_sing\":{},\"base_like\":{},\"extra_like\":{},\"score\":{},\"tags\":{{{}}}}}",
            escape_json(&self.family),
            self.prime,
            escape_json(&self.label),
            self.total_sing,
            self.node_like,
            self.bad_sing,
            self.base_like,
            self.extra_like,
            self.score,
            tags
        )
    }

    fn tags_tsv(&self) -> String {
        self.tags
            .iter()
            .map(|(key, value)| format!("{key}={value}"))
            .collect::<Vec<_>>()
            .join(";")
    }
}

pub fn score_projective_surface<const P: i64>(
    input: &ProjectiveSurfaceScorerInput<P>,
) -> FiniteFieldSingularityStats<P> {
    let surface = FiniteFieldSurfaceView::new(input.polynomial.clone());
    let line_pairs = input
        .plane_product_skeleton
        .as_ref()
        .map(|skeleton| plane_line_pairs(skeleton.planes.len()))
        .unwrap_or_default();
    let mut line_profile = vec![0; line_pairs.len()];
    let mut singular_points = Vec::new();

    for coords in projective_points::<P, P3_VARIABLE_COUNT>() {
        if !surface.is_singular_at(&coords) {
            continue;
        }

        let hessian_rank = surface.hessian_rank_at(&coords);
        let (incident_planes, incident_lines, base_like) =
            if let Some(skeleton) = input.plane_product_skeleton.as_ref() {
                let incident_planes = incident_planes(&skeleton.planes, &coords);
                let incident_lines = incident_line_pairs(&incident_planes);
                let base_like = hessian_rank == 3
                    && !incident_lines.is_empty()
                    && skeleton.quartic_r.evaluate(&coords).is_zero();
                (incident_planes, incident_lines, base_like)
            } else {
                (Vec::new(), Vec::new(), false)
            };

        if base_like {
            for line in &incident_lines {
                let line_index = line_pairs
                    .iter()
                    .position(|candidate| candidate == line)
                    .expect("incident line should be a known plane pair");
                line_profile[line_index] += 1;
            }
        }

        singular_points.push(FiniteFieldSingularPoint {
            coords,
            hessian_rank,
            plane_multiplicity: incident_planes.len(),
            incident_lines,
            base_like,
        });
    }

    let total_sing = singular_points.len();
    let node_like_points = singular_points
        .iter()
        .filter(|point| point.hessian_rank == 3)
        .map(|point| point.coords)
        .collect::<Vec<_>>();
    let node_like = node_like_points.len();
    let base_like = singular_points
        .iter()
        .filter(|point| point.hessian_rank == 3 && point.base_like)
        .count();
    let orbit_profile = orbit_profile(input.symmetry(), &node_like_points);

    FiniteFieldSingularityStats {
        total_sing,
        node_like,
        bad_sing: total_sing - node_like,
        base_like,
        extra_like: node_like - base_like,
        line_profile,
        orbit_profile,
        singular_points,
    }
}

pub fn score_plane_product_base_lines<const P: i64>(
    skeleton: &PlaneProductSkeleton<P>,
) -> BaseLineLengthStats {
    let line_pairs = plane_line_pairs(skeleton.planes.len());
    let line_checks = line_pairs
        .iter()
        .map(|&line| {
            let basis = line_basis(&skeleton.planes[line.0], &skeleton.planes[line.1]);
            let restriction = restrict_p3_to_line(&skeleton.quartic_r, basis);
            BaseLineLengthCheck {
                line,
                degree: restriction.degree(),
                squarefree: super::homogeneous_binary_is_squarefree(&restriction),
                visible_roots: super::count_binary_projective_roots(&restriction),
            }
        })
        .collect();

    BaseLineLengthStats {
        line_checks,
        triple_plane_bad_points: count_triple_plane_bad_points(skeleton),
    }
}

pub fn projective_p3_points<const P: i64>() -> Vec<ProjectivePointFp<P>> {
    projective_points::<P, P3_VARIABLE_COUNT>()
}

pub fn projective_p2_points<const P: i64>() -> Vec<ProjectivePlanePointFp<P>> {
    projective_points::<P, 3>()
}

pub fn projective_p1_points<const P: i64>() -> Vec<ProjectiveLinePointFp<P>> {
    projective_points::<P, 2>()
}

pub fn normalize_projective_point<const P: i64, const N: usize>(coords: [Fp<P>; N]) -> [Fp<P>; N] {
    let pivot = coords
        .iter()
        .find(|coord| !coord.is_zero())
        .copied()
        .expect("projective point cannot be zero");
    coords.map(|coord| coord / pivot)
}

pub fn projective_point_key<const P: i64, const N: usize>(coords: &[Fp<P>; N]) -> [i64; N] {
    coords.map(Fp::value)
}

pub fn key_to_projective_point<const P: i64, const N: usize>(key: [i64; N]) -> [Fp<P>; N] {
    key.map(Fp::new)
}

pub fn linear_form<const P: i64>(coefficients: PlaneFp<P>) -> SurfacePolynomialFp<P> {
    coefficients.into_iter().enumerate().fold(
        SurfacePolynomialFp::<P>::zero(),
        |sum, (variable, coefficient)| {
            sum.add(&SurfacePolynomialFp::<P>::variable(variable).scale(coefficient))
        },
    )
}

pub fn line_basis<const P: i64>(
    first: &PlaneFp<P>,
    second: &PlaneFp<P>,
) -> [ProjectivePointFp<P>; 2] {
    let nullspace = Matrix::from_rows(vec![first.to_vec(), second.to_vec()]).nullspace();
    assert_eq!(nullspace.len(), 2, "expected two planes to meet in a line");
    [
        vec_to_projective_point(nullspace[0].clone()),
        vec_to_projective_point(nullspace[1].clone()),
    ]
}

pub fn restrict_p3_to_line<const P: i64>(
    polynomial: &SurfacePolynomialFp<P>,
    basis: [ProjectivePointFp<P>; 2],
) -> super::BinaryPolynomialFp<P> {
    let [s, t] = std::array::from_fn(super::BinaryPolynomialFp::<P>::variable);
    let forms: [super::BinaryPolynomialFp<P>; P3_VARIABLE_COUNT] =
        std::array::from_fn(|variable| {
            s.scale(basis[0][variable])
                .add(&t.scale(basis[1][variable]))
        });

    polynomial
        .terms()
        .into_iter()
        .fold(super::BinaryPolynomialFp::<P>::zero(), |sum, term| {
            let substituted = term.exponents().into_iter().enumerate().fold(
                super::BinaryPolynomialFp::<P>::constant(term.coefficient()),
                |product, (variable, exponent)| product.mul(&forms[variable].pow_usize(exponent)),
            );
            sum.add(&substituted)
        })
}

pub fn square_roots<const P: i64>(value: Fp<P>) -> Vec<Fp<P>> {
    (0..P)
        .map(Fp::<P>::new)
        .filter(|root| *root * *root == value)
        .collect()
}

pub fn symmetry_orbit_points<const P: i64>(
    symmetry: &SurfaceSymmetry<P>,
    seed: ProjectivePointFp<P>,
) -> Vec<ProjectivePointFp<P>> {
    symmetry_orbit(symmetry, seed)
}

pub(crate) fn legacy_surface_input<const P: i64>(
    polynomial: SurfacePolynomialFp<P>,
    quartic_r: SurfacePolynomialFp<P>,
    planes: Vec<PlaneFp<P>>,
    symmetry: super::FiniteFieldSymmetry,
    sqrt2: Option<Fp<P>>,
) -> ProjectiveSurfaceScorerInput<P> {
    let core_symmetry = match symmetry {
        super::FiniteFieldSymmetry::D4TimesZ2 => SurfaceSymmetry::D4TimesZ2,
        super::FiniteFieldSymmetry::D8TimesZ2 => SurfaceSymmetry::D8TimesZ2 {
            sqrt2: sqrt2.expect("D8 finite-field symmetry needs sqrt(2)"),
        },
    };

    ProjectiveSurfaceScorerInput::new(polynomial)
        .with_plane_product_skeleton(PlaneProductSkeleton::new(planes, quartic_r))
        .with_symmetry(core_symmetry)
}

struct FiniteFieldSurfaceView<const P: i64> {
    polynomial: SurfacePolynomialFp<P>,
    gradient: [SurfacePolynomialFp<P>; P3_VARIABLE_COUNT],
    hessian: [[SurfacePolynomialFp<P>; P3_VARIABLE_COUNT]; P3_VARIABLE_COUNT],
}

impl<const P: i64> FiniteFieldSurfaceView<P> {
    fn new(polynomial: SurfacePolynomialFp<P>) -> Self {
        let gradient: [SurfacePolynomialFp<P>; P3_VARIABLE_COUNT] =
            std::array::from_fn(|variable| polynomial.partial_derivative(variable));
        let hessian = std::array::from_fn(|row| {
            std::array::from_fn(|col| gradient[row].partial_derivative(col))
        });

        Self {
            polynomial,
            gradient,
            hessian,
        }
    }

    fn is_singular_at(&self, coords: &ProjectivePointFp<P>) -> bool {
        self.polynomial.evaluate(coords).is_zero()
            && self
                .gradient
                .iter()
                .all(|partial| partial.evaluate(coords).is_zero())
    }

    fn hessian_rank_at(&self, coords: &ProjectivePointFp<P>) -> usize {
        Matrix::from_rows(
            self.hessian
                .iter()
                .map(|row| row.iter().map(|entry| entry.evaluate(coords)).collect())
                .collect(),
        )
        .rank()
    }
}

fn projective_points<const P: i64, const N: usize>() -> Vec<[Fp<P>; N]> {
    let mut points = Vec::new();
    for first_nonzero in 0..N {
        let free_count = N - first_nonzero - 1;
        let mut suffix = vec![0; free_count];
        loop {
            let mut coords = [Fp::<P>::zero(); N];
            coords[first_nonzero] = Fp::one();
            for (offset, value) in suffix.iter().enumerate() {
                coords[first_nonzero + 1 + offset] = Fp::new(*value);
            }
            points.push(coords);

            if !increment_base_p_digits::<P>(&mut suffix) {
                break;
            }
        }
    }
    points
}

fn increment_base_p_digits<const P: i64>(digits: &mut [i64]) -> bool {
    if digits.is_empty() {
        return false;
    }

    for digit in digits.iter_mut().rev() {
        *digit += 1;
        if *digit < P {
            return true;
        }
        *digit = 0;
    }
    false
}

fn count_triple_plane_bad_points<const P: i64>(skeleton: &PlaneProductSkeleton<P>) -> usize {
    let mut bad_points = BTreeSet::new();
    let mut degenerate_triples = 0;
    for first in 0..skeleton.planes.len() {
        for second in (first + 1)..skeleton.planes.len() {
            for third in (second + 1)..skeleton.planes.len() {
                let nullspace = Matrix::from_rows(vec![
                    skeleton.planes[first].to_vec(),
                    skeleton.planes[second].to_vec(),
                    skeleton.planes[third].to_vec(),
                ])
                .nullspace();
                match nullspace.len() {
                    0 => {}
                    1 => {
                        let point = normalize_projective_point(vec_to_projective_point(
                            nullspace[0].clone(),
                        ));
                        if skeleton.quartic_r.evaluate(&point).is_zero() {
                            bad_points.insert(projective_point_key(&point));
                        }
                    }
                    _ => degenerate_triples += 1,
                }
            }
        }
    }
    bad_points.len() + degenerate_triples
}

fn incident_planes<const P: i64>(
    planes: &[PlaneFp<P>],
    coords: &ProjectivePointFp<P>,
) -> Vec<usize> {
    planes
        .iter()
        .enumerate()
        .filter_map(|(index, plane)| plane_eval(plane, coords).is_zero().then_some(index))
        .collect()
}

fn plane_eval<const P: i64>(plane: &PlaneFp<P>, coords: &ProjectivePointFp<P>) -> Fp<P> {
    plane
        .iter()
        .zip(coords)
        .fold(Fp::zero(), |sum, (coefficient, coord)| {
            sum + *coefficient * *coord
        })
}

fn plane_line_pairs(plane_count: usize) -> Vec<(usize, usize)> {
    let mut pairs = Vec::new();
    for first in 0..plane_count {
        for second in (first + 1)..plane_count {
            pairs.push((first, second));
        }
    }
    pairs
}

fn incident_line_pairs(incident_planes: &[usize]) -> Vec<(usize, usize)> {
    let mut pairs = Vec::new();
    for (position, &first) in incident_planes.iter().enumerate() {
        for &second in &incident_planes[(position + 1)..] {
            pairs.push((first, second));
        }
    }
    pairs
}

fn orbit_profile<const P: i64>(
    symmetry: &SurfaceSymmetry<P>,
    node_like_points: &[ProjectivePointFp<P>],
) -> BTreeMap<usize, usize> {
    let node_keys: BTreeSet<_> = node_like_points.iter().map(projective_point_key).collect();
    let mut unseen = node_keys.clone();
    let mut profile = BTreeMap::new();

    while let Some(seed) = unseen.iter().next().copied() {
        let seed_point = key_to_projective_point(seed);
        let orbit = symmetry_orbit(symmetry, seed_point);
        let node_orbit: BTreeSet<_> = orbit
            .into_iter()
            .map(|point| projective_point_key(&point))
            .filter(|key| node_keys.contains(key))
            .collect();
        let orbit_size = node_orbit.len();
        *profile.entry(orbit_size).or_insert(0) += 1;
        for key in node_orbit {
            unseen.remove(&key);
        }
    }

    profile
}

fn symmetry_orbit<const P: i64>(
    symmetry: &SurfaceSymmetry<P>,
    seed: ProjectivePointFp<P>,
) -> Vec<ProjectivePointFp<P>> {
    let mut seen = BTreeSet::new();
    let mut queue = VecDeque::from([normalize_projective_point(seed)]);

    while let Some(point) = queue.pop_front() {
        if !seen.insert(projective_point_key(&point)) {
            continue;
        }

        for transformed in symmetry_generators(symmetry, &point) {
            let normalized = normalize_projective_point(transformed);
            if !seen.contains(&projective_point_key(&normalized)) {
                queue.push_back(normalized);
            }
        }
    }

    seen.into_iter().map(key_to_projective_point).collect()
}

fn symmetry_generators<const P: i64>(
    symmetry: &SurfaceSymmetry<P>,
    point: &ProjectivePointFp<P>,
) -> Vec<ProjectivePointFp<P>> {
    let [x, y, z, w] = *point;
    let z_reflection = [x, y, -z, w];
    match symmetry {
        SurfaceSymmetry::None => Vec::new(),
        SurfaceSymmetry::D4TimesZ2 => vec![[-y, x, z, w], [x, -y, z, w], z_reflection],
        SurfaceSymmetry::D8TimesZ2 { sqrt2 } => {
            let half_sqrt2 = *sqrt2 / Fp::new(2);
            vec![
                [(x - y) * half_sqrt2, (x + y) * half_sqrt2, z, w],
                [x, -y, z, w],
                z_reflection,
            ]
        }
        SurfaceSymmetry::Explicit(generators) => generators
            .iter()
            .map(|generator| generator.apply(point))
            .collect(),
    }
}

fn vec_to_projective_point<const P: i64>(vector: Vec<Fp<P>>) -> ProjectivePointFp<P> {
    vector
        .try_into()
        .unwrap_or_else(|_| panic!("expected a length-{P3_VARIABLE_COUNT} vector"))
}

fn escape_json(value: &str) -> String {
    value
        .chars()
        .flat_map(|ch| match ch {
            '"' => "\\\"".chars().collect::<Vec<_>>(),
            '\\' => "\\\\".chars().collect(),
            '\n' => "\\n".chars().collect(),
            '\r' => "\\r".chars().collect(),
            '\t' => "\\t".chars().collect(),
            _ => vec![ch],
        })
        .collect()
}
