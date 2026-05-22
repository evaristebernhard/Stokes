use nodal_core::{
    FieldElement, HomogeneousPolynomialP3, Matrix, P3_VARIABLE_COUNT, QuadraticRational, Rational,
    SparsePolynomial,
};
use std::collections::{BTreeMap, BTreeSet};
use std::ops::{Add, Div, Mul, Neg, Sub};

pub mod critical_profile;
pub mod search_core;

type Q2 = QuadraticRational;
type PolynomialP3 = SparsePolynomial<Q2, P3_VARIABLE_COUNT>;
type BinaryPolynomial = SparsePolynomial<Q2, 2>;
type TernaryPolynomial = SparsePolynomial<Q2, 3>;
pub type BinaryPolynomialFp<const P: i64> = SparsePolynomial<Fp<P>, 2>;
pub type TernaryPolynomialFp<const P: i64> = SparsePolynomial<Fp<P>, 3>;
type AxisLiftFp<const P: i64> = fn([Fp<P>; 2]) -> [Fp<P>; 3];
type AxisRestrictionFp<const P: i64> = (BinaryPolynomialFp<P>, AxisLiftFp<P>);

pub const ENDRASS_DEGREE: usize = 8;
pub const ENDRASS_PLANE_COUNT: usize = 8;
pub const ENDRASS_INTERSECTION_LINE_COUNT: usize = 28;
pub const ENDRASS_BASIC_LINE_INTERSECTION_LENGTH: usize = 4;
pub const ENDRASS_BASIC_NODE_COUNT: usize = 112;
pub const ENDRASS_EXTRA_NODE_COUNT: usize = 56;
pub const ENDRASS_TOTAL_NODE_COUNT: usize = 168;
pub const ENDRASS_MIYAOKA_UPPER_BOUND: usize = 174;
pub const ENDRASS_VARCHENKO_DEGREE8_BOUND: usize = 180;

pub type PolynomialP3Fp<const P: i64> = SparsePolynomial<Fp<P>, P3_VARIABLE_COUNT>;
const D4_R_PARAMETER_COUNT: usize = 7;

#[derive(Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd)]
pub struct Fp<const P: i64> {
    value: i64,
}

impl<const P: i64> Fp<P> {
    pub fn new(value: i64) -> Self {
        assert!(P > 1, "finite-field modulus must be greater than one");
        Self {
            value: value.rem_euclid(P),
        }
    }

    pub fn value(self) -> i64 {
        self.value
    }

    pub fn inv(self) -> Self {
        assert!(!self.is_zero(), "cannot invert zero in a finite field");
        let (gcd, inverse, _) = extended_gcd_i64(self.value, P);
        assert_eq!(gcd, 1, "finite-field modulus must be prime here");
        Self::new(inverse)
    }
}

impl<const P: i64> From<i64> for Fp<P> {
    fn from(value: i64) -> Self {
        Self::new(value)
    }
}

impl<const P: i64> Add for Fp<P> {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        Self::new(self.value + rhs.value)
    }
}

impl<const P: i64> Sub for Fp<P> {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self::Output {
        Self::new(self.value - rhs.value)
    }
}

impl<const P: i64> Mul for Fp<P> {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self::Output {
        Self::new(self.value * rhs.value)
    }
}

#[allow(clippy::suspicious_arithmetic_impl)]
impl<const P: i64> Div for Fp<P> {
    type Output = Self;

    fn div(self, rhs: Self) -> Self::Output {
        self * rhs.inv()
    }
}

impl<const P: i64> Neg for Fp<P> {
    type Output = Self;

    fn neg(self) -> Self::Output {
        Self::new(-self.value)
    }
}

impl<const P: i64> FieldElement for Fp<P> {
    fn zero() -> Self {
        Self::new(0)
    }

    fn one() -> Self {
        Self::new(1)
    }

    fn is_zero(&self) -> bool {
        self.value == 0
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct NestedQ2 {
    rational: Q2,
    irrational: Q2,
    radicand: Option<Q2>,
}

impl NestedQ2 {
    fn new(rational: Q2, irrational: Q2, radicand: Option<Q2>) -> Self {
        if irrational.is_zero() {
            Self {
                rational,
                irrational: q(0),
                radicand: None,
            }
        } else {
            Self {
                rational,
                irrational,
                radicand: Some(radicand.expect("nested quadratic element needs a radicand")),
            }
        }
    }

    fn from_q2(value: Q2) -> Self {
        Self::new(value, q(0), None)
    }

    fn sqrt(radicand: Q2) -> Self {
        Self::new(q(0), q(1), Some(radicand))
    }

    fn common_radicand(self, rhs: Self) -> Option<Q2> {
        match (self.radicand, rhs.radicand) {
            (None, None) => None,
            (Some(radicand), None) | (None, Some(radicand)) => Some(radicand),
            (Some(lhs), Some(rhs)) => {
                assert_eq!(lhs, rhs, "nested quadratic radicands must match");
                Some(lhs)
            }
        }
    }
}

impl Add for NestedQ2 {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        Self::new(
            self.rational + rhs.rational,
            self.irrational + rhs.irrational,
            self.common_radicand(rhs),
        )
    }
}

impl Sub for NestedQ2 {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self::Output {
        self + (-rhs)
    }
}

impl Mul for NestedQ2 {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self::Output {
        let radicand = self.common_radicand(rhs);
        let radicand_value = radicand.unwrap_or_else(|| q(0));
        Self::new(
            self.rational * rhs.rational + self.irrational * rhs.irrational * radicand_value,
            self.rational * rhs.irrational + self.irrational * rhs.rational,
            radicand,
        )
    }
}

impl Div for NestedQ2 {
    type Output = Self;

    fn div(self, rhs: Self) -> Self::Output {
        let radicand = self.common_radicand(rhs);
        let radicand_value = radicand.unwrap_or_else(|| q(0));
        let norm = rhs.rational * rhs.rational - rhs.irrational * rhs.irrational * radicand_value;
        self * Self::new(rhs.rational / norm, -rhs.irrational / norm, radicand)
    }
}

impl Neg for NestedQ2 {
    type Output = Self;

    fn neg(self) -> Self::Output {
        Self::new(-self.rational, -self.irrational, self.radicand)
    }
}

impl FieldElement for NestedQ2 {
    fn zero() -> Self {
        Self::from_q2(q(0))
    }

    fn one() -> Self {
        Self::from_q2(q(1))
    }

    fn is_zero(&self) -> bool {
        self.rational.is_zero() && self.irrational.is_zero()
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct D4FamilyParameters<const P: i64> {
    pub axis_offset: Fp<P>,
    pub diagonal_offset: Fp<P>,
    pub plane_scale: Fp<P>,
    pub a: Fp<P>,
    pub h: Fp<P>,
    pub b: Fp<P>,
    pub d: Fp<P>,
    pub e: Fp<P>,
    pub g: Fp<P>,
    pub i: Fp<P>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum FiniteFieldSymmetry {
    D4TimesZ2,
    D8TimesZ2,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct FiniteFieldScorerInput<const P: i64> {
    polynomial: PolynomialP3Fp<P>,
    quartic_r: PolynomialP3Fp<P>,
    planes: Vec<[Fp<P>; P3_VARIABLE_COUNT]>,
    symmetry: FiniteFieldSymmetry,
    sqrt2: Option<Fp<P>>,
}

impl<const P: i64> FiniteFieldScorerInput<P> {
    pub fn endrass(sqrt2_value: i64) -> Self {
        let sqrt2 = Fp::new(sqrt2_value);
        Self {
            polynomial: reduce_q2_polynomial_mod_p(&endrass_octic_polynomial(), sqrt2),
            quartic_r: reduce_q2_polynomial_mod_p(&endrass_quartic_r_polynomial(), sqrt2),
            planes: endrass_planes_mod_p(sqrt2),
            symmetry: FiniteFieldSymmetry::D8TimesZ2,
            sqrt2: Some(sqrt2),
        }
    }

    pub fn d4_family(parameters: D4FamilyParameters<P>) -> Self {
        let polynomial = d4_family_polynomial_mod_p(parameters);
        let quartic_r = d4_family_quartic_r_mod_p(parameters);
        Self {
            polynomial,
            quartic_r,
            planes: d4_family_planes_mod_p(parameters),
            symmetry: FiniteFieldSymmetry::D4TimesZ2,
            sqrt2: None,
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct FiniteFieldSingularPoint<const P: i64> {
    coords: [Fp<P>; P3_VARIABLE_COUNT],
    hessian_rank: usize,
    plane_multiplicity: usize,
    incident_lines: Vec<(usize, usize)>,
    base_like: bool,
}

impl<const P: i64> FiniteFieldSingularPoint<P> {
    pub fn coords(&self) -> [Fp<P>; P3_VARIABLE_COUNT] {
        self.coords
    }

    pub fn hessian_rank(&self) -> usize {
        self.hessian_rank
    }

    pub fn plane_multiplicity(&self) -> usize {
        self.plane_multiplicity
    }

    pub fn incident_lines(&self) -> &[(usize, usize)] {
        &self.incident_lines
    }

    pub fn base_like(&self) -> bool {
        self.base_like
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct FiniteFieldSingularityStats<const P: i64> {
    total_sing: usize,
    node_like: usize,
    bad_sing: usize,
    base_like: usize,
    extra_like: usize,
    line_profile: Vec<usize>,
    orbit_profile: BTreeMap<usize, usize>,
    singular_points: Vec<FiniteFieldSingularPoint<P>>,
}

impl<const P: i64> FiniteFieldSingularityStats<P> {
    pub fn total_sing(&self) -> usize {
        self.total_sing
    }

    pub fn node_like(&self) -> usize {
        self.node_like
    }

    pub fn bad_sing(&self) -> usize {
        self.bad_sing
    }

    pub fn base_like(&self) -> usize {
        self.base_like
    }

    pub fn extra_like(&self) -> usize {
        self.extra_like
    }

    pub fn line_profile(&self) -> &[usize] {
        &self.line_profile
    }

    pub fn orbit_profile(&self) -> &BTreeMap<usize, usize> {
        &self.orbit_profile
    }

    pub fn singular_points(&self) -> &[FiniteFieldSingularPoint<P>] {
        &self.singular_points
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum D4ReflectionPlane {
    AxisY0,
    DiagonalXEqualsY,
}

impl D4ReflectionPlane {
    pub fn label(self) -> &'static str {
        match self {
            Self::AxisY0 => "axis-y0",
            Self::DiagonalXEqualsY => "diag-x-eq-y",
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum D4EventKind {
    OffAxisNode,
    ZAxisContact,
    WAxisContact,
}

impl D4EventKind {
    pub fn label(self) -> &'static str {
        match self {
            Self::OffAxisNode => "off-axis-node",
            Self::ZAxisContact => "z-axis-contact",
            Self::WAxisContact => "w-axis-contact",
        }
    }

    fn derivative_variables(self) -> &'static [usize] {
        match self {
            Self::OffAxisNode => &[0, 1, 2],
            Self::ZAxisContact => &[0, 2],
            Self::WAxisContact => &[0, 1],
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct D4LinearEvent<const P: i64> {
    reflection_plane: D4ReflectionPlane,
    kind: D4EventKind,
    point: [Fp<P>; 3],
    rho: Fp<P>,
}

impl<const P: i64> D4LinearEvent<P> {
    pub fn reflection_plane(&self) -> D4ReflectionPlane {
        self.reflection_plane
    }

    pub fn kind(&self) -> D4EventKind {
        self.kind
    }

    pub fn point(&self) -> [Fp<P>; 3] {
        self.point
    }

    pub fn rho(&self) -> Fp<P> {
        self.rho
    }

    pub fn signature(&self) -> String {
        format!(
            "{}:{}:[{},{},{}]:rho={}",
            self.reflection_plane.label(),
            self.kind.label(),
            self.point[0].value(),
            self.point[1].value(),
            self.point[2].value(),
            self.rho.value()
        )
    }

    pub fn json_fragment(&self) -> String {
        format!(
            "{{\"plane\":\"{}\",\"kind\":\"{}\",\"point\":[{},{},{}],\"rho\":{}}}",
            self.reflection_plane.label(),
            self.kind.label(),
            self.point[0].value(),
            self.point[1].value(),
            self.point[2].value(),
            self.rho.value()
        )
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PlaneQuarticEventScan {
    reflection_label: &'static str,
    off_axis_nodes: usize,
    z_axis_contacts: usize,
    w_axis_contacts: usize,
    linear_factors: usize,
    node_orbit_size: usize,
    contact_orbit_size: usize,
}

impl PlaneQuarticEventScan {
    pub fn reflection_label(&self) -> &'static str {
        self.reflection_label
    }

    pub fn off_axis_nodes(&self) -> usize {
        self.off_axis_nodes
    }

    pub fn z_axis_contacts(&self) -> usize {
        self.z_axis_contacts
    }

    pub fn w_axis_contacts(&self) -> usize {
        self.w_axis_contacts
    }

    pub fn linear_factors(&self) -> usize {
        self.linear_factors
    }

    pub fn predicted_orbit_contribution(&self) -> usize {
        self.off_axis_nodes * self.node_orbit_size
            + (self.z_axis_contacts + self.w_axis_contacts) * self.contact_orbit_size
    }

    pub fn signature(&self) -> String {
        format!(
            "{}:nodes={},z_contacts={},w_contacts={},linear_factors={}",
            self.reflection_label,
            self.off_axis_nodes,
            self.z_axis_contacts,
            self.w_axis_contacts,
            self.linear_factors
        )
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct BaseLineLengthCheck {
    line: (usize, usize),
    degree: usize,
    squarefree: bool,
    visible_roots: usize,
}

impl BaseLineLengthCheck {
    pub fn line(&self) -> (usize, usize) {
        self.line
    }

    pub fn degree(&self) -> usize {
        self.degree
    }

    pub fn squarefree(&self) -> bool {
        self.squarefree
    }

    pub fn visible_roots(&self) -> usize {
        self.visible_roots
    }

    pub fn algebraic_closure_length(&self) -> usize {
        if self.degree == ENDRASS_BASIC_LINE_INTERSECTION_LENGTH && self.squarefree {
            ENDRASS_BASIC_LINE_INTERSECTION_LENGTH
        } else {
            0
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct BaseLineLengthStats {
    line_checks: Vec<BaseLineLengthCheck>,
    triple_plane_bad_points: usize,
}

impl BaseLineLengthStats {
    pub fn line_checks(&self) -> &[BaseLineLengthCheck] {
        &self.line_checks
    }

    pub fn triple_plane_bad_points(&self) -> usize {
        self.triple_plane_bad_points
    }

    pub fn algebraic_closure_length(&self) -> usize {
        if self.triple_plane_bad_points == 0 {
            self.line_checks
                .iter()
                .map(BaseLineLengthCheck::algebraic_closure_length)
                .sum()
        } else {
            0
        }
    }

    pub fn visible_root_count(&self) -> usize {
        self.line_checks
            .iter()
            .map(BaseLineLengthCheck::visible_roots)
            .sum()
    }

    pub fn all_lines_degree_four_squarefree(&self) -> bool {
        self.line_checks
            .iter()
            .all(|line| line.degree == ENDRASS_BASIC_LINE_INTERSECTION_LENGTH && line.squarefree)
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct D4SearchCandidate<const P: i64> {
    parameters: D4FamilyParameters<P>,
    singularity_stats: FiniteFieldSingularityStats<P>,
    base_length_stats: BaseLineLengthStats,
    event_scans: Vec<PlaneQuarticEventScan>,
    score: isize,
}

impl<const P: i64> D4SearchCandidate<P> {
    pub fn parameters(&self) -> D4FamilyParameters<P> {
        self.parameters
    }

    pub fn singularity_stats(&self) -> &FiniteFieldSingularityStats<P> {
        &self.singularity_stats
    }

    pub fn base_length_stats(&self) -> &BaseLineLengthStats {
        &self.base_length_stats
    }

    pub fn event_scans(&self) -> &[PlaneQuarticEventScan] {
        &self.event_scans
    }

    pub fn score(&self) -> isize {
        self.score
    }

    pub fn tsv_header() -> &'static str {
        "prime\tscore\ttotal\tnode\tbad\tbase_fp\textra\tbase_ac\tbase_visible\tevents\tparams"
    }

    pub fn to_tsv(&self) -> String {
        let event_signature = self
            .event_scans
            .iter()
            .map(PlaneQuarticEventScan::signature)
            .collect::<Vec<_>>()
            .join("|");
        format!(
            "{P}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}",
            self.score,
            self.singularity_stats.total_sing(),
            self.singularity_stats.node_like(),
            self.singularity_stats.bad_sing(),
            self.singularity_stats.base_like(),
            self.singularity_stats.extra_like(),
            self.base_length_stats.algebraic_closure_length(),
            self.base_length_stats.visible_root_count(),
            event_signature,
            format_d4_parameters(self.parameters)
        )
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct D4EventSearchOptions {
    pub max_event_set_size: usize,
    pub max_free_dimension: usize,
    pub solution_scan_limit: usize,
    pub candidate_limit: usize,
    pub require_base_112: bool,
    pub require_no_bad_singularities: bool,
    pub require_no_linear_factors: bool,
}

impl Default for D4EventSearchOptions {
    fn default() -> Self {
        Self {
            max_event_set_size: 2,
            max_free_dimension: 1,
            solution_scan_limit: 200,
            candidate_limit: 20,
            require_base_112: true,
            require_no_bad_singularities: true,
            require_no_linear_factors: true,
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct D4GeneratedCandidate<const P: i64> {
    seed_events: Vec<D4LinearEvent<P>>,
    free_dimension: usize,
    candidate: D4SearchCandidate<P>,
}

impl<const P: i64> D4GeneratedCandidate<P> {
    pub fn seed_events(&self) -> &[D4LinearEvent<P>] {
        &self.seed_events
    }

    pub fn free_dimension(&self) -> usize {
        self.free_dimension
    }

    pub fn candidate(&self) -> &D4SearchCandidate<P> {
        &self.candidate
    }

    pub fn tsv_header() -> &'static str {
        "seed_event_count\tfree_dim\tseed_events\tprime\tscore\ttotal\tnode\tbad\tbase_fp\textra\tbase_ac\tbase_visible\tevents\tparams"
    }

    pub fn to_tsv(&self) -> String {
        let seed_events = self
            .seed_events
            .iter()
            .map(D4LinearEvent::signature)
            .collect::<Vec<_>>()
            .join("|");
        format!(
            "{}\t{}\t{}\t{}",
            self.seed_events.len(),
            self.free_dimension,
            seed_events,
            self.candidate.to_tsv()
        )
    }

    pub fn to_json_line(&self) -> String {
        let seed_events = self
            .seed_events
            .iter()
            .map(D4LinearEvent::json_fragment)
            .collect::<Vec<_>>()
            .join(",");
        let event_scans = self
            .candidate
            .event_scans()
            .iter()
            .map(|scan| {
                format!(
                    "{{\"plane\":\"{}\",\"off_axis_nodes\":{},\"z_axis_contacts\":{},\"w_axis_contacts\":{},\"linear_factors\":{},\"predicted_orbit_contribution\":{}}}",
                    scan.reflection_label(),
                    scan.off_axis_nodes(),
                    scan.z_axis_contacts(),
                    scan.w_axis_contacts(),
                    scan.linear_factors(),
                    scan.predicted_orbit_contribution()
                )
            })
            .collect::<Vec<_>>()
            .join(",");
        format!(
            "{{\"prime\":{P},\"seed_event_count\":{},\"free_dimension\":{},\"seed_events\":[{}],\"score\":{},\"total\":{},\"node\":{},\"bad\":{},\"base_fp\":{},\"extra\":{},\"base_ac\":{},\"base_visible\":{},\"event_scans\":[{}],\"parameters\":{}}}",
            self.seed_events.len(),
            self.free_dimension,
            seed_events,
            self.candidate.score(),
            self.candidate.singularity_stats().total_sing(),
            self.candidate.singularity_stats().node_like(),
            self.candidate.singularity_stats().bad_sing(),
            self.candidate.singularity_stats().base_like(),
            self.candidate.singularity_stats().extra_like(),
            self.candidate
                .base_length_stats()
                .algebraic_closure_length(),
            self.candidate.base_length_stats().visible_root_count(),
            event_scans,
            format_d4_parameters_json(self.candidate.parameters())
        )
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct EndrassPrimeCalibration {
    prime: i64,
    sqrt2: i64,
    global_visible_nodes: usize,
    global_bad_singularities: usize,
    base_algebraic_closure_length: usize,
    base_visible_roots: usize,
    segre_event_orbit_contribution: usize,
}

impl EndrassPrimeCalibration {
    pub fn prime(&self) -> i64 {
        self.prime
    }

    pub fn sqrt2(&self) -> i64 {
        self.sqrt2
    }

    pub fn global_visible_nodes(&self) -> usize {
        self.global_visible_nodes
    }

    pub fn global_bad_singularities(&self) -> usize {
        self.global_bad_singularities
    }

    pub fn base_algebraic_closure_length(&self) -> usize {
        self.base_algebraic_closure_length
    }

    pub fn base_visible_roots(&self) -> usize {
        self.base_visible_roots
    }

    pub fn segre_event_orbit_contribution(&self) -> usize {
        self.segre_event_orbit_contribution
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct OcticSurface {
    polynomial: HomogeneousPolynomialP3<Q2>,
}

impl OcticSurface {
    pub fn new(polynomial: HomogeneousPolynomialP3<Q2>) -> Self {
        assert_eq!(polynomial.degree(), ENDRASS_DEGREE);
        Self { polynomial }
    }

    pub fn polynomial(&self) -> &HomogeneousPolynomialP3<Q2> {
        &self.polynomial
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct EndrassPlane {
    index: usize,
    coefficients: [Q2; P3_VARIABLE_COUNT],
}

impl EndrassPlane {
    pub fn index(self) -> usize {
        self.index
    }

    pub fn coefficients(self) -> [Q2; P3_VARIABLE_COUNT] {
        self.coefficients
    }

    pub fn linear_form(self) -> PolynomialP3 {
        linear_form(self.coefficients)
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct EndrassIntersectionLine {
    first_plane: usize,
    second_plane: usize,
}

impl EndrassIntersectionLine {
    pub fn new(first_plane: usize, second_plane: usize) -> Self {
        assert!(first_plane < second_plane);
        assert!(second_plane < ENDRASS_PLANE_COUNT);
        Self {
            first_plane,
            second_plane,
        }
    }

    pub fn planes(self) -> (usize, usize) {
        (self.first_plane, self.second_plane)
    }

    pub fn basis(self) -> [[Q2; P3_VARIABLE_COUNT]; 2] {
        let first = endrass_plane(self.first_plane).coefficients().to_vec();
        let second = endrass_plane(self.second_plane).coefficients().to_vec();
        let nullspace = Matrix::from_rows(vec![first, second]).nullspace();
        assert_eq!(nullspace.len(), 2);

        [
            vec_to_p3(nullspace[0].clone()),
            vec_to_p3(nullspace[1].clone()),
        ]
    }

    pub fn quartic_restriction(self) -> BinaryPolynomial {
        restrict_p3_to_line(&endrass_quartic_r_polynomial(), self.basis())
    }

    pub fn quartic_intersection_length(self) -> usize {
        self.quartic_restriction().degree()
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct EndrassBasicNodeOrbitCandidate {
    separation: usize,
    representative_line: EndrassIntersectionLine,
    line_orbit_size: usize,
    quartic_intersection_length: usize,
}

impl EndrassBasicNodeOrbitCandidate {
    pub fn separation(self) -> usize {
        self.separation
    }

    pub fn representative_line(self) -> EndrassIntersectionLine {
        self.representative_line
    }

    pub fn line_orbit_size(self) -> usize {
        self.line_orbit_size
    }

    pub fn quartic_intersection_length(self) -> usize {
        self.quartic_intersection_length
    }

    pub fn contribution(self) -> usize {
        self.line_orbit_size * self.quartic_intersection_length
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum EndrassReflectionPlane {
    E0,
    E1,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum EndrassExtraEventKind {
    Node,
    AxisContact,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct EndrassExtraNodeEvent {
    label: &'static str,
    reflection_plane: EndrassReflectionPlane,
    kind: EndrassExtraEventKind,
    segre_point: [Q2; 3],
    surface_orbit_size: usize,
}

impl EndrassExtraNodeEvent {
    pub fn label(self) -> &'static str {
        self.label
    }

    pub fn reflection_plane(self) -> EndrassReflectionPlane {
        self.reflection_plane
    }

    pub fn kind(self) -> EndrassExtraEventKind {
        self.kind
    }

    pub fn segre_point(self) -> [Q2; 3] {
        self.segre_point
    }

    pub fn surface_orbit_size(self) -> usize {
        self.surface_orbit_size
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum SegreCoordinateAxis {
    Z,
    W,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct EndrassSegreEventVerification {
    label: &'static str,
    kind: EndrassExtraEventKind,
    quotient_value_zero: bool,
    quotient_gradient_zero: bool,
    quotient_hessian_rank: usize,
    contact_axis: Option<SegreCoordinateAxis>,
    axis_contact: bool,
    lift_singular: bool,
    lift_hessian_rank: usize,
}

impl EndrassSegreEventVerification {
    pub fn label(&self) -> &'static str {
        self.label
    }

    pub fn kind(&self) -> EndrassExtraEventKind {
        self.kind
    }

    pub fn quotient_value_zero(&self) -> bool {
        self.quotient_value_zero
    }

    pub fn quotient_gradient_zero(&self) -> bool {
        self.quotient_gradient_zero
    }

    pub fn quotient_hessian_rank(&self) -> usize {
        self.quotient_hessian_rank
    }

    pub fn contact_axis(&self) -> Option<SegreCoordinateAxis> {
        self.contact_axis
    }

    pub fn axis_contact(&self) -> bool {
        self.axis_contact
    }

    pub fn lift_singular(&self) -> bool {
        self.lift_singular
    }

    pub fn lift_hessian_rank(&self) -> usize {
        self.lift_hessian_rank
    }

    pub fn verified(&self) -> bool {
        let quotient_verified = match self.kind {
            EndrassExtraEventKind::Node => {
                self.quotient_value_zero
                    && self.quotient_gradient_zero
                    && self.quotient_hessian_rank == 2
            }
            EndrassExtraEventKind::AxisContact => self.quotient_value_zero && self.axis_contact,
        };

        quotient_verified && self.lift_singular && self.lift_hessian_rank == 3
    }
}

pub fn endrass_octic() -> OcticSurface {
    OcticSurface::new(HomogeneousPolynomialP3::from(endrass_octic_polynomial()))
}

/// Endrass's final octic in coordinates `[x:y:z:w]`, written as `F=P-R^2`.
pub fn endrass_octic_polynomial() -> PolynomialP3 {
    endrass_plane_product_polynomial().sub(&endrass_quartic_r_polynomial().pow_usize(2))
}

pub fn endrass_plane_product_polynomial() -> PolynomialP3 {
    endrass_planes()
        .into_iter()
        .map(EndrassPlane::linear_form)
        .fold(PolynomialP3::constant(q(1)), |product, factor| {
            product.mul(&factor)
        })
}

pub fn endrass_quadratic_factor_product_polynomial() -> PolynomialP3 {
    let [x, y, _z, w] = variables();
    let first = x.pow_usize(2).sub(&w.pow_usize(2));
    let second = y.pow_usize(2).sub(&w.pow_usize(2));
    let third = x.add(&y).pow_usize(2).sub(&w.pow_usize(2).scale(q(2)));
    let fourth = x.sub(&y).pow_usize(2).sub(&w.pow_usize(2).scale(q(2)));

    first.mul(&second).mul(&third).mul(&fourth).scale(qr(1, 4))
}

pub fn endrass_quartic_r_polynomial() -> PolynomialP3 {
    let [x, y, z, w] = variables();
    let radius_squared = x.pow_usize(2).add(&y.pow_usize(2));
    let params = EndrassParameters::final_parameters();

    radius_squared
        .pow_usize(2)
        .scale(params.a)
        .add(
            &radius_squared.mul(
                &z.pow_usize(2)
                    .scale(params.b)
                    .add(&w.pow_usize(2).scale(params.d)),
            ),
        )
        .add(&z.pow_usize(4).scale(params.e))
        .add(&z.pow_usize(2).mul(&w.pow_usize(2)).scale(params.g))
        .add(&w.pow_usize(4).scale(params.i))
}

pub fn endrass_planes() -> Vec<EndrassPlane> {
    (0..ENDRASS_PLANE_COUNT).map(endrass_plane).collect()
}

pub fn endrass_plane(index: usize) -> EndrassPlane {
    assert!(index < ENDRASS_PLANE_COUNT);
    let (cos, sin) = octagon_cos_sin(index);
    EndrassPlane {
        index,
        coefficients: [cos, sin, q(0), q(-1)],
    }
}

pub fn endrass_intersection_lines() -> Vec<EndrassIntersectionLine> {
    let mut lines = Vec::with_capacity(ENDRASS_INTERSECTION_LINE_COUNT);
    for first in 0..ENDRASS_PLANE_COUNT {
        for second in (first + 1)..ENDRASS_PLANE_COUNT {
            lines.push(EndrassIntersectionLine::new(first, second));
        }
    }
    lines
}

pub fn endrass_basic_node_orbit_candidates() -> Vec<EndrassBasicNodeOrbitCandidate> {
    (1..=4)
        .map(|separation| {
            let representative_line = EndrassIntersectionLine::new(0, separation);
            let line_orbit_size = if separation == 4 { 4 } else { 8 };
            EndrassBasicNodeOrbitCandidate {
                separation,
                representative_line,
                line_orbit_size,
                quartic_intersection_length: representative_line.quartic_intersection_length(),
            }
        })
        .collect()
}

pub fn endrass_basic_node_count_from_line_structure() -> usize {
    endrass_intersection_lines()
        .into_iter()
        .map(EndrassIntersectionLine::quartic_intersection_length)
        .sum()
}

pub fn endrass_basic_node_count_from_orbits() -> usize {
    endrass_basic_node_orbit_candidates()
        .into_iter()
        .map(EndrassBasicNodeOrbitCandidate::contribution)
        .sum()
}

pub fn endrass_extra_node_events() -> Vec<EndrassExtraNodeEvent> {
    vec![
        EndrassExtraNodeEvent {
            label: "s3",
            reflection_plane: EndrassReflectionPlane::E0,
            kind: EndrassExtraEventKind::Node,
            segre_point: [q(8) * (sqrt2() - q(1)), q(1), q(4)],
            surface_orbit_size: 16,
        },
        EndrassExtraNodeEvent {
            label: "t3",
            reflection_plane: EndrassReflectionPlane::E0,
            kind: EndrassExtraEventKind::AxisContact,
            segre_point: [q(1), q(0), q(2)],
            surface_orbit_size: 8,
        },
        EndrassExtraNodeEvent {
            label: "u5",
            reflection_plane: EndrassReflectionPlane::E1,
            kind: EndrassExtraEventKind::Node,
            segre_point: [q(2) * (q(3) - q(2) * sqrt2()), q(3) - q(2) * sqrt2(), q(4)],
            surface_orbit_size: 16,
        },
        EndrassExtraNodeEvent {
            label: "v1",
            reflection_plane: EndrassReflectionPlane::E1,
            kind: EndrassExtraEventKind::AxisContact,
            segre_point: [q(1), q(3) + q(2) * sqrt2(), q(0)],
            surface_orbit_size: 8,
        },
        EndrassExtraNodeEvent {
            label: "v2",
            reflection_plane: EndrassReflectionPlane::E1,
            kind: EndrassExtraEventKind::AxisContact,
            segre_point: [q(1), q(0), q(4)],
            surface_orbit_size: 8,
        },
    ]
}

pub fn endrass_extra_node_count_from_segre_events() -> usize {
    endrass_extra_node_events()
        .into_iter()
        .map(EndrassExtraNodeEvent::surface_orbit_size)
        .sum()
}

pub fn endrass_segre_quotient(plane: EndrassReflectionPlane) -> TernaryPolynomial {
    let restricted = restrict_octic_to_reflection_plane(plane);
    segre_quotient_from_even_ternary(&restricted)
}

pub fn verify_endrass_segre_events() -> Vec<EndrassSegreEventVerification> {
    endrass_extra_node_events()
        .into_iter()
        .map(verify_endrass_segre_event)
        .collect()
}

pub fn endrass_structural_node_count() -> usize {
    endrass_basic_node_count_from_orbits() + endrass_extra_node_count_from_segre_events()
}

pub fn miyaoka_node_bound(degree: usize) -> usize {
    4 * degree * (degree - 1).pow(2) / 9
}

pub fn varchenko_arnold_number_degree8() -> usize {
    let mut count = 0;
    for k0 in 1..=7 {
        for k1 in 1..=7 {
            for k2 in 1..=7 {
                for k3 in 1..=7 {
                    if k0 + k1 + k2 + k3 == 13 {
                        count += 1;
                    }
                }
            }
        }
    }
    count
}

pub fn rotation_45_pullback(polynomial: &PolynomialP3) -> PolynomialP3 {
    let [x, y, z, w] = variables();
    let half_sqrt2 = qsqrt(1, 2);
    let forms = [
        x.scale(half_sqrt2).sub(&y.scale(half_sqrt2)),
        x.scale(half_sqrt2).add(&y.scale(half_sqrt2)),
        z,
        w,
    ];
    substitute_p3(polynomial, &forms)
}

pub fn y_reflection_pullback(polynomial: &PolynomialP3) -> PolynomialP3 {
    let [x, y, z, w] = variables();
    substitute_p3(polynomial, &[x, y.scale(q(-1)), z, w])
}

pub fn z_reflection_pullback(polynomial: &PolynomialP3) -> PolynomialP3 {
    let [x, y, z, w] = variables();
    substitute_p3(polynomial, &[x, y, z.scale(q(-1)), w])
}

pub fn score_finite_field_singularities<const P: i64>(
    input: &FiniteFieldScorerInput<P>,
) -> FiniteFieldSingularityStats<P> {
    search_core::score_projective_surface(&search_core::legacy_surface_input(
        input.polynomial.clone(),
        input.quartic_r.clone(),
        input.planes.clone(),
        input.symmetry,
        input.sqrt2,
    ))
}

pub fn endrass_finite_field_stats_mod_31() -> FiniteFieldSingularityStats<31> {
    score_finite_field_singularities(&FiniteFieldScorerInput::<31>::endrass(8))
}

pub fn d4_family_polynomial_mod_p<const P: i64>(
    parameters: D4FamilyParameters<P>,
) -> PolynomialP3Fp<P> {
    d4_family_plane_product_mod_p(parameters)
        .sub(&d4_family_quartic_r_mod_p(parameters).pow_usize(2))
}

pub fn d4_family_plane_product_mod_p<const P: i64>(
    parameters: D4FamilyParameters<P>,
) -> PolynomialP3Fp<P> {
    d4_family_planes_mod_p(parameters)
        .into_iter()
        .map(linear_form_fp)
        .fold(
            PolynomialP3Fp::<P>::constant(parameters.plane_scale),
            |product, factor| product.mul(&factor),
        )
}

pub fn d4_family_quartic_r_mod_p<const P: i64>(
    parameters: D4FamilyParameters<P>,
) -> PolynomialP3Fp<P> {
    let basis = d4_quartic_r_basis_mod_p::<P>();
    [
        parameters.a,
        parameters.h,
        parameters.b,
        parameters.d,
        parameters.e,
        parameters.g,
        parameters.i,
    ]
    .into_iter()
    .zip(basis)
    .fold(PolynomialP3Fp::<P>::zero(), |sum, (coefficient, basis)| {
        sum.add(&basis.scale(coefficient))
    })
}

fn d4_quartic_r_basis_mod_p<const P: i64>() -> Vec<PolynomialP3Fp<P>> {
    let [x, y, z, w] = variables_fp();
    let radius_squared = x.pow_usize(2).add(&y.pow_usize(2));

    vec![
        radius_squared.pow_usize(2),
        x.pow_usize(2).mul(&y.pow_usize(2)),
        radius_squared.mul(&z.pow_usize(2)),
        radius_squared.mul(&w.pow_usize(2)),
        z.pow_usize(4),
        z.pow_usize(2).mul(&w.pow_usize(2)),
        w.pow_usize(4),
    ]
}

pub fn endrass_parameters_mod_p<const P: i64>(sqrt2_value: i64) -> D4FamilyParameters<P> {
    let sqrt2 = Fp::<P>::new(sqrt2_value);
    let two = Fp::<P>::new(2);
    let half = Fp::<P>::new(2).inv();
    D4FamilyParameters {
        axis_offset: Fp::one(),
        diagonal_offset: sqrt2,
        plane_scale: Fp::new(4).inv(),
        a: -Fp::new(4).inv() * (Fp::one() + sqrt2),
        h: Fp::zero(),
        b: half * (two + sqrt2),
        d: Fp::new(8).inv() * (two + Fp::new(7) * sqrt2),
        e: -Fp::one(),
        g: half * (Fp::one() - two * sqrt2),
        i: -Fp::new(16).inv() * (Fp::one() + Fp::new(12) * sqrt2),
    }
}

pub fn scan_d4_candidate<const P: i64>(parameters: D4FamilyParameters<P>) -> D4SearchCandidate<P> {
    let input = FiniteFieldScorerInput::d4_family(parameters);
    let singularity_stats = score_finite_field_singularities(&input);
    let base_length_stats = score_basic_line_lengths(&input);
    let event_scans = scan_d4_segre_events(parameters);
    let score = candidate_score(&singularity_stats, &base_length_stats, &event_scans);

    D4SearchCandidate {
        parameters,
        singularity_stats,
        base_length_stats,
        event_scans,
        score,
    }
}

pub fn scan_d4_local_window<const P: i64>(
    center: D4FamilyParameters<P>,
    radius: i64,
    limit: usize,
) -> Vec<D4SearchCandidate<P>> {
    let offsets: Vec<i64> = (-radius..=radius).collect();
    let mut candidates = Vec::new();

    for &h_offset in &offsets {
        for &g_offset in &offsets {
            for &i_offset in &offsets {
                let mut parameters = center;
                parameters.h = center.h + Fp::new(h_offset);
                parameters.g = center.g + Fp::new(g_offset);
                parameters.i = center.i + Fp::new(i_offset);
                candidates.push(scan_d4_candidate(parameters));
            }
        }
    }

    candidates.sort_by_key(|candidate| std::cmp::Reverse(candidate.score));
    candidates.truncate(limit);
    candidates
}

pub fn enumerate_d4_linear_events<const P: i64>(
    fixed_plane_parameters: D4FamilyParameters<P>,
) -> Vec<D4LinearEvent<P>> {
    assert!(P != 2, "event linearization requires odd characteristic");
    [
        D4ReflectionPlane::AxisY0,
        D4ReflectionPlane::DiagonalXEqualsY,
    ]
    .into_iter()
    .flat_map(|reflection_plane| {
        enumerate_d4_linear_events_on_plane(fixed_plane_parameters, reflection_plane)
    })
    .collect()
}

pub fn generate_d4_event_candidates<const P: i64>(
    fixed_plane_parameters: D4FamilyParameters<P>,
    options: D4EventSearchOptions,
) -> Vec<D4GeneratedCandidate<P>> {
    let events = enumerate_d4_linear_events(fixed_plane_parameters);
    let max_event_set_size = options.max_event_set_size.max(1).min(events.len());
    let mut generated = Vec::new();
    let mut seen_parameters = BTreeSet::new();
    let mut scanned_solutions = 0usize;

    'event_size: for event_set_size in 1..=max_event_set_size {
        let mut event_indices = Vec::with_capacity(event_set_size);
        let keep_searching = visit_index_combinations(
            events.len(),
            event_set_size,
            0,
            &mut event_indices,
            &mut |indices| {
                let seed_events = indices
                    .iter()
                    .map(|&index| events[index])
                    .collect::<Vec<_>>();
                let rows = d4_linear_event_rows(fixed_plane_parameters, &seed_events);
                let Some(solution) = solve_d4_affine_linear_system(&rows) else {
                    return true;
                };
                if solution.free_dimension() > options.max_free_dimension {
                    return true;
                }

                visit_affine_solutions(&solution, &mut |coefficients| {
                    scanned_solutions += 1;
                    if scanned_solutions > options.solution_scan_limit {
                        return false;
                    }

                    let parameters =
                        d4_parameters_from_r_coefficients(fixed_plane_parameters, coefficients);
                    if !seen_parameters.insert(d4_parameter_key(parameters)) {
                        return true;
                    }
                    let Some(candidate) = build_filtered_d4_candidate(parameters, options) else {
                        return true;
                    };
                    generated.push(D4GeneratedCandidate {
                        seed_events: seed_events.clone(),
                        free_dimension: solution.free_dimension(),
                        candidate,
                    });
                    true
                })
            },
        );
        if !keep_searching || scanned_solutions > options.solution_scan_limit {
            break 'event_size;
        }
    }

    generated.sort_by_key(|candidate| std::cmp::Reverse(candidate.candidate().score()));
    generated.truncate(options.candidate_limit);
    generated
}

pub fn score_basic_line_lengths<const P: i64>(
    input: &FiniteFieldScorerInput<P>,
) -> BaseLineLengthStats {
    search_core::PlaneProductSkeleton::new(input.planes.clone(), input.quartic_r.clone())
        .base_line_length_stats()
}

pub fn scan_d4_segre_events<const P: i64>(
    parameters: D4FamilyParameters<P>,
) -> Vec<PlaneQuarticEventScan> {
    [
        D4ReflectionPlane::AxisY0,
        D4ReflectionPlane::DiagonalXEqualsY,
    ]
    .into_iter()
    .map(|plane| {
        scan_plane_quartic_events(
            plane.label(),
            &d4_segre_quotient_mod_p(parameters, plane),
            8,
            4,
        )
    })
    .collect()
}

pub fn d4_segre_quotient_mod_p<const P: i64>(
    parameters: D4FamilyParameters<P>,
    plane: D4ReflectionPlane,
) -> TernaryPolynomialFp<P> {
    let polynomial = d4_family_polynomial_mod_p(parameters);
    let forms = d4_reflection_plane_forms_fp(plane);
    segre_quotient_from_even_ternary_fp(&substitute_p3_to_ternary_fp(&polynomial, &forms))
}

fn d4_plane_product_quotient_mod_p<const P: i64>(
    parameters: D4FamilyParameters<P>,
    plane: D4ReflectionPlane,
) -> TernaryPolynomialFp<P> {
    let polynomial = d4_family_plane_product_mod_p(parameters);
    let forms = d4_reflection_plane_forms_fp(plane);
    segre_quotient_from_even_ternary_fp(&substitute_p3_to_ternary_fp(&polynomial, &forms))
}

fn d4_r_quotient_basis_mod_p<const P: i64>(
    plane: D4ReflectionPlane,
) -> Vec<TernaryPolynomialFp<P>> {
    let forms = d4_reflection_plane_forms_fp(plane);
    d4_quartic_r_basis_mod_p::<P>()
        .into_iter()
        .map(|basis| {
            segre_quotient_from_even_ternary_fp(&substitute_p3_to_ternary_fp(&basis, &forms))
        })
        .collect()
}

fn d4_reflection_plane_forms_fp<const P: i64>(
    plane: D4ReflectionPlane,
) -> [TernaryPolynomialFp<P>; P3_VARIABLE_COUNT] {
    let [u, z, w] = ternary_variables_fp();
    match plane {
        D4ReflectionPlane::AxisY0 => [u, TernaryPolynomialFp::zero(), z, w],
        D4ReflectionPlane::DiagonalXEqualsY => [u.clone(), u, z, w],
    }
}

pub fn endrass_segre_quotient_mod_p<const P: i64>(
    plane: EndrassReflectionPlane,
    sqrt2_value: i64,
) -> TernaryPolynomialFp<P> {
    let sqrt2 = Fp::<P>::new(sqrt2_value);
    let polynomial = reduce_q2_polynomial_mod_p(&endrass_octic_polynomial(), sqrt2);
    let [u, z, w] = ternary_variables_fp();
    let forms = match plane {
        EndrassReflectionPlane::E0 => [u, TernaryPolynomialFp::zero(), z, w],
        EndrassReflectionPlane::E1 => [u.scale(Fp::one() + sqrt2), u, z, w],
    };
    segre_quotient_from_even_ternary_fp(&substitute_p3_to_ternary_fp(&polynomial, &forms))
}

pub fn scan_endrass_segre_events_mod_p<const P: i64>(
    sqrt2_value: i64,
) -> Vec<PlaneQuarticEventScan> {
    [
        (EndrassReflectionPlane::E0, "E0"),
        (EndrassReflectionPlane::E1, "E1"),
    ]
    .into_iter()
    .map(|(plane, label)| {
        scan_plane_quartic_events(
            label,
            &endrass_segre_quotient_mod_p::<P>(plane, sqrt2_value),
            16,
            8,
        )
    })
    .collect()
}

pub fn endrass_multi_prime_calibrations() -> Vec<EndrassPrimeCalibration> {
    vec![
        endrass_prime_calibration_31(),
        endrass_prime_calibration_41(),
        endrass_prime_calibration_73(),
        endrass_prime_calibration_89(),
    ]
}

pub fn endrass_prime_calibration_31() -> EndrassPrimeCalibration {
    endrass_prime_calibration::<31>(8)
}

pub fn endrass_prime_calibration_41() -> EndrassPrimeCalibration {
    endrass_prime_calibration::<41>(17)
}

pub fn endrass_prime_calibration_73() -> EndrassPrimeCalibration {
    endrass_prime_calibration::<73>(32)
}

pub fn endrass_prime_calibration_89() -> EndrassPrimeCalibration {
    endrass_prime_calibration::<89>(25)
}

fn endrass_prime_calibration<const P: i64>(sqrt2_value: i64) -> EndrassPrimeCalibration {
    let input = FiniteFieldScorerInput::<P>::endrass(sqrt2_value);
    let global = score_finite_field_singularities(&input);
    let base = score_basic_line_lengths(&input);
    let segre_event_orbit_contribution = scan_endrass_segre_events_mod_p::<P>(sqrt2_value)
        .iter()
        .map(PlaneQuarticEventScan::predicted_orbit_contribution)
        .sum();

    EndrassPrimeCalibration {
        prime: P,
        sqrt2: sqrt2_value,
        global_visible_nodes: global.node_like(),
        global_bad_singularities: global.bad_sing(),
        base_algebraic_closure_length: base.algebraic_closure_length(),
        base_visible_roots: base.visible_root_count(),
        segre_event_orbit_contribution,
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct EndrassParameters {
    a: Q2,
    b: Q2,
    d: Q2,
    e: Q2,
    g: Q2,
    i: Q2,
}

impl EndrassParameters {
    fn final_parameters() -> Self {
        Self {
            a: -qr(1, 4) * (q(1) + sqrt2()),
            b: qr(1, 2) * (q(2) + sqrt2()),
            d: qr(1, 8) * (q(2) + q(7) * sqrt2()),
            e: q(-1),
            g: qr(1, 2) * (q(1) - q(2) * sqrt2()),
            i: -qr(1, 16) * (q(1) + q(12) * sqrt2()),
        }
    }
}

fn variables() -> [PolynomialP3; P3_VARIABLE_COUNT] {
    std::array::from_fn(PolynomialP3::variable)
}

fn variables_fp<const P: i64>() -> [PolynomialP3Fp<P>; P3_VARIABLE_COUNT] {
    std::array::from_fn(PolynomialP3Fp::<P>::variable)
}

fn binary_variables() -> [BinaryPolynomial; 2] {
    std::array::from_fn(BinaryPolynomial::variable)
}

fn binary_variables_fp<const P: i64>() -> [BinaryPolynomialFp<P>; 2] {
    std::array::from_fn(BinaryPolynomialFp::<P>::variable)
}

fn ternary_variables_fp<const P: i64>() -> [TernaryPolynomialFp<P>; 3] {
    std::array::from_fn(TernaryPolynomialFp::<P>::variable)
}

fn linear_form(coefficients: [Q2; P3_VARIABLE_COUNT]) -> PolynomialP3 {
    coefficients.into_iter().enumerate().fold(
        PolynomialP3::zero(),
        |sum, (variable, coefficient)| {
            sum.add(&PolynomialP3::variable(variable).scale(coefficient))
        },
    )
}

fn linear_form_fp<const P: i64>(coefficients: [Fp<P>; P3_VARIABLE_COUNT]) -> PolynomialP3Fp<P> {
    coefficients.into_iter().enumerate().fold(
        PolynomialP3Fp::<P>::zero(),
        |sum, (variable, coefficient)| {
            sum.add(&PolynomialP3Fp::<P>::variable(variable).scale(coefficient))
        },
    )
}

fn candidate_score<const P: i64>(
    singularity_stats: &FiniteFieldSingularityStats<P>,
    base_length_stats: &BaseLineLengthStats,
    event_scans: &[PlaneQuarticEventScan],
) -> isize {
    let event_bonus: usize = event_scans
        .iter()
        .map(PlaneQuarticEventScan::predicted_orbit_contribution)
        .sum();
    singularity_stats.node_like() as isize + event_bonus as isize
        - 1000 * singularity_stats.bad_sing() as isize
        - 25 * (ENDRASS_BASIC_NODE_COUNT as isize
            - base_length_stats.algebraic_closure_length() as isize)
            .abs()
        - 500 * base_length_stats.triple_plane_bad_points() as isize
}

fn enumerate_d4_linear_events_on_plane<const P: i64>(
    fixed_plane_parameters: D4FamilyParameters<P>,
    reflection_plane: D4ReflectionPlane,
) -> Vec<D4LinearEvent<P>> {
    let plane_product = d4_plane_product_quotient_mod_p(fixed_plane_parameters, reflection_plane);
    let mut events = Vec::new();

    for point in projective_points_p2_mod_p::<P>()
        .into_iter()
        .filter(|point| point.iter().all(|coord| !coord.is_zero()))
    {
        events.extend(d4_linear_events_at_point(
            reflection_plane,
            D4EventKind::OffAxisNode,
            point,
            &plane_product,
        ));
    }

    for binary_point in projective_points_p1_mod_p::<P>()
        .into_iter()
        .filter(|point| point.iter().all(|coord| !coord.is_zero()))
    {
        events.extend(d4_linear_events_at_point(
            reflection_plane,
            D4EventKind::ZAxisContact,
            [binary_point[0], Fp::zero(), binary_point[1]],
            &plane_product,
        ));
        events.extend(d4_linear_events_at_point(
            reflection_plane,
            D4EventKind::WAxisContact,
            [binary_point[0], binary_point[1], Fp::zero()],
            &plane_product,
        ));
    }

    events
}

fn d4_linear_events_at_point<const P: i64>(
    reflection_plane: D4ReflectionPlane,
    kind: D4EventKind,
    point: [Fp<P>; 3],
    plane_product: &TernaryPolynomialFp<P>,
) -> Vec<D4LinearEvent<P>> {
    square_roots_fp(plane_product.evaluate(&point))
        .into_iter()
        .filter(|rho| !rho.is_zero())
        .map(|rho| D4LinearEvent {
            reflection_plane,
            kind,
            point,
            rho,
        })
        .collect()
}

fn d4_linear_event_rows<const P: i64>(
    fixed_plane_parameters: D4FamilyParameters<P>,
    events: &[D4LinearEvent<P>],
) -> Vec<[Fp<P>; D4_R_PARAMETER_COUNT + 1]> {
    events
        .iter()
        .flat_map(|event| d4_single_linear_event_rows(fixed_plane_parameters, *event))
        .collect()
}

fn d4_single_linear_event_rows<const P: i64>(
    fixed_plane_parameters: D4FamilyParameters<P>,
    event: D4LinearEvent<P>,
) -> Vec<[Fp<P>; D4_R_PARAMETER_COUNT + 1]> {
    let basis = d4_r_quotient_basis_mod_p(event.reflection_plane);
    let plane_product =
        d4_plane_product_quotient_mod_p(fixed_plane_parameters, event.reflection_plane);
    let mut rows = Vec::with_capacity(1 + event.kind.derivative_variables().len());

    rows.push(linear_event_row(&basis, event.point, event.rho, None));
    let denominator = Fp::<P>::new(2) * event.rho;
    for &variable in event.kind.derivative_variables() {
        let rhs = plane_product
            .partial_derivative(variable)
            .evaluate(&event.point)
            / denominator;
        rows.push(linear_event_row(&basis, event.point, rhs, Some(variable)));
    }

    rows
}

fn linear_event_row<const P: i64>(
    basis: &[TernaryPolynomialFp<P>],
    point: [Fp<P>; 3],
    rhs: Fp<P>,
    derivative_variable: Option<usize>,
) -> [Fp<P>; D4_R_PARAMETER_COUNT + 1] {
    assert_eq!(basis.len(), D4_R_PARAMETER_COUNT);
    std::array::from_fn(|index| {
        if index == D4_R_PARAMETER_COUNT {
            return rhs;
        }
        match derivative_variable {
            Some(variable) => basis[index].partial_derivative(variable).evaluate(&point),
            None => basis[index].evaluate(&point),
        }
    })
}

fn build_filtered_d4_candidate<const P: i64>(
    parameters: D4FamilyParameters<P>,
    options: D4EventSearchOptions,
) -> Option<D4SearchCandidate<P>> {
    let input = FiniteFieldScorerInput::d4_family(parameters);
    let base_length_stats = score_basic_line_lengths(&input);
    if options.require_base_112
        && (base_length_stats.algebraic_closure_length() != ENDRASS_BASIC_NODE_COUNT
            || base_length_stats.triple_plane_bad_points() != 0)
    {
        return None;
    }

    let event_scans = scan_d4_segre_events(parameters);
    if options.require_no_linear_factors && event_scans.iter().any(|scan| scan.linear_factors() > 0)
    {
        return None;
    }

    let singularity_stats = score_finite_field_singularities(&input);
    if options.require_no_bad_singularities && singularity_stats.bad_sing() > 0 {
        return None;
    }

    let score = candidate_score(&singularity_stats, &base_length_stats, &event_scans);
    Some(D4SearchCandidate {
        parameters,
        singularity_stats,
        base_length_stats,
        event_scans,
        score,
    })
}

fn d4_parameters_from_r_coefficients<const P: i64>(
    fixed_plane_parameters: D4FamilyParameters<P>,
    coefficients: [Fp<P>; D4_R_PARAMETER_COUNT],
) -> D4FamilyParameters<P> {
    D4FamilyParameters {
        axis_offset: fixed_plane_parameters.axis_offset,
        diagonal_offset: fixed_plane_parameters.diagonal_offset,
        plane_scale: fixed_plane_parameters.plane_scale,
        a: coefficients[0],
        h: coefficients[1],
        b: coefficients[2],
        d: coefficients[3],
        e: coefficients[4],
        g: coefficients[5],
        i: coefficients[6],
    }
}

#[cfg(test)]
fn d4_r_coefficients<const P: i64>(
    parameters: D4FamilyParameters<P>,
) -> [Fp<P>; D4_R_PARAMETER_COUNT] {
    [
        parameters.a,
        parameters.h,
        parameters.b,
        parameters.d,
        parameters.e,
        parameters.g,
        parameters.i,
    ]
}

fn d4_parameter_key<const P: i64>(parameters: D4FamilyParameters<P>) -> [i64; 10] {
    [
        parameters.axis_offset.value(),
        parameters.diagonal_offset.value(),
        parameters.plane_scale.value(),
        parameters.a.value(),
        parameters.h.value(),
        parameters.b.value(),
        parameters.d.value(),
        parameters.e.value(),
        parameters.g.value(),
        parameters.i.value(),
    ]
}

fn format_d4_parameters<const P: i64>(parameters: D4FamilyParameters<P>) -> String {
    format!(
        "axis={},diag={},scale={},a={},h={},b={},d={},e={},g={},i={}",
        parameters.axis_offset.value(),
        parameters.diagonal_offset.value(),
        parameters.plane_scale.value(),
        parameters.a.value(),
        parameters.h.value(),
        parameters.b.value(),
        parameters.d.value(),
        parameters.e.value(),
        parameters.g.value(),
        parameters.i.value()
    )
}

fn format_d4_parameters_json<const P: i64>(parameters: D4FamilyParameters<P>) -> String {
    format!(
        "{{\"axis\":{},\"diag\":{},\"scale\":{},\"a\":{},\"h\":{},\"b\":{},\"d\":{},\"e\":{},\"g\":{},\"i\":{}}}",
        parameters.axis_offset.value(),
        parameters.diagonal_offset.value(),
        parameters.plane_scale.value(),
        parameters.a.value(),
        parameters.h.value(),
        parameters.b.value(),
        parameters.d.value(),
        parameters.e.value(),
        parameters.g.value(),
        parameters.i.value()
    )
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct AffineLinearSolution<const P: i64, const N: usize> {
    particular: [Fp<P>; N],
    basis: Vec<[Fp<P>; N]>,
}

impl<const P: i64, const N: usize> AffineLinearSolution<P, N> {
    fn free_dimension(&self) -> usize {
        self.basis.len()
    }
}

fn solve_d4_affine_linear_system<const P: i64>(
    rows: &[[Fp<P>; D4_R_PARAMETER_COUNT + 1]],
) -> Option<AffineLinearSolution<P, D4_R_PARAMETER_COUNT>> {
    const N: usize = D4_R_PARAMETER_COUNT;
    if rows.is_empty() {
        return Some(AffineLinearSolution {
            particular: [Fp::zero(); N],
            basis: (0..N)
                .map(|free_col| {
                    std::array::from_fn(|index| {
                        if index == free_col {
                            Fp::one()
                        } else {
                            Fp::zero()
                        }
                    })
                })
                .collect(),
        });
    }

    let mut matrix = rows.iter().map(|row| row.to_vec()).collect::<Vec<_>>();
    let mut pivots = Vec::new();
    let mut pivot_row = 0usize;

    for col in 0..N {
        let Some(row_with_pivot) =
            (pivot_row..matrix.len()).find(|&row| !matrix[row][col].is_zero())
        else {
            continue;
        };

        matrix.swap(pivot_row, row_with_pivot);
        let pivot = matrix[pivot_row][col];
        for entry in &mut matrix[pivot_row] {
            *entry = *entry / pivot;
        }

        let pivot_values = matrix[pivot_row].clone();
        for (row, matrix_row) in matrix.iter_mut().enumerate() {
            if row == pivot_row {
                continue;
            }
            let factor = matrix_row[col];
            if factor.is_zero() {
                continue;
            }
            for (entry, pivot_entry) in matrix_row.iter_mut().zip(&pivot_values) {
                *entry = *entry - factor * *pivot_entry;
            }
        }

        pivots.push(col);
        pivot_row += 1;
        if pivot_row == matrix.len() {
            break;
        }
    }

    for row in &matrix {
        if row[..N].iter().all(FieldElement::is_zero) && !row[N].is_zero() {
            return None;
        }
    }

    let mut is_pivot_col = [false; N];
    for &pivot in &pivots {
        is_pivot_col[pivot] = true;
    }
    let free_cols = (0..N).filter(|&col| !is_pivot_col[col]).collect::<Vec<_>>();

    let mut particular = [Fp::<P>::zero(); N];
    for (row, &pivot_col) in pivots.iter().enumerate() {
        particular[pivot_col] = matrix[row][N];
    }

    let basis = free_cols
        .into_iter()
        .map(|free_col| {
            let mut vector = [Fp::<P>::zero(); N];
            vector[free_col] = Fp::one();
            for (row, &pivot_col) in pivots.iter().enumerate() {
                vector[pivot_col] = -matrix[row][free_col];
            }
            vector
        })
        .collect();

    Some(AffineLinearSolution { particular, basis })
}

#[cfg(test)]
fn enumerate_affine_solutions<const P: i64, const N: usize>(
    solution: &AffineLinearSolution<P, N>,
) -> Vec<[Fp<P>; N]> {
    let mut results = Vec::new();
    visit_affine_solutions(solution, &mut |point| {
        results.push(point);
        true
    });
    results
}

fn visit_affine_solutions<const P: i64, const N: usize>(
    solution: &AffineLinearSolution<P, N>,
    visit: &mut impl FnMut([Fp<P>; N]) -> bool,
) -> bool {
    let mut digits = vec![0; solution.basis.len()];
    loop {
        let mut point = solution.particular;
        for (digit, basis_vector) in digits.iter().zip(&solution.basis) {
            let scale = Fp::<P>::new(*digit);
            for (entry, basis_entry) in point.iter_mut().zip(basis_vector) {
                *entry = *entry + scale * *basis_entry;
            }
        }
        if !visit(point) {
            return false;
        }

        if !increment_base_p_digits::<P>(&mut digits) {
            break;
        }
    }
    true
}

fn visit_index_combinations(
    len: usize,
    size: usize,
    start: usize,
    current: &mut Vec<usize>,
    visit: &mut impl FnMut(&[usize]) -> bool,
) -> bool {
    if current.len() == size {
        return visit(current);
    }

    let remaining = size - current.len();
    for index in start..=len - remaining {
        current.push(index);
        if !visit_index_combinations(len, size, index + 1, current, visit) {
            return false;
        }
        current.pop();
    }
    true
}

fn square_roots_fp<const P: i64>(value: Fp<P>) -> Vec<Fp<P>> {
    (0..P)
        .map(Fp::<P>::new)
        .filter(|root| *root * *root == value)
        .collect()
}

#[cfg(test)]
fn d4_event_constraints_hold<const P: i64>(
    parameters: D4FamilyParameters<P>,
    event: D4LinearEvent<P>,
) -> bool {
    let coefficients = d4_r_coefficients(parameters);
    d4_single_linear_event_rows(parameters, event)
        .into_iter()
        .all(|row| {
            let lhs = row[..D4_R_PARAMETER_COUNT]
                .iter()
                .zip(coefficients)
                .fold(Fp::<P>::zero(), |sum, (coefficient, parameter)| {
                    sum + *coefficient * parameter
                });
            lhs == row[D4_R_PARAMETER_COUNT]
        })
}

fn octagon_cos_sin(index: usize) -> (Q2, Q2) {
    let half_sqrt2 = qsqrt(1, 2);
    match index % 8 {
        0 => (q(1), q(0)),
        1 => (half_sqrt2, half_sqrt2),
        2 => (q(0), q(1)),
        3 => (-half_sqrt2, half_sqrt2),
        4 => (q(-1), q(0)),
        5 => (-half_sqrt2, -half_sqrt2),
        6 => (q(0), q(-1)),
        7 => (half_sqrt2, -half_sqrt2),
        _ => unreachable!(),
    }
}

fn d4_family_planes_mod_p<const P: i64>(
    parameters: D4FamilyParameters<P>,
) -> Vec<[Fp<P>; P3_VARIABLE_COUNT]> {
    let zero = Fp::<P>::zero();
    let one = Fp::<P>::one();
    let alpha = parameters.axis_offset;
    let beta = parameters.diagonal_offset;

    vec![
        [one, zero, zero, -alpha],
        [one, zero, zero, alpha],
        [zero, one, zero, -alpha],
        [zero, one, zero, alpha],
        [one, one, zero, -beta],
        [one, one, zero, beta],
        [one, -one, zero, -beta],
        [one, -one, zero, beta],
    ]
}

fn endrass_planes_mod_p<const P: i64>(sqrt2: Fp<P>) -> Vec<[Fp<P>; P3_VARIABLE_COUNT]> {
    endrass_planes()
        .into_iter()
        .map(|plane| {
            plane
                .coefficients()
                .map(|coefficient| q2_mod_p(coefficient, sqrt2))
        })
        .collect()
}

fn homogeneous_binary_is_squarefree<const P: i64>(polynomial: &BinaryPolynomialFp<P>) -> bool {
    if polynomial.is_zero() || polynomial.degree() != ENDRASS_BASIC_LINE_INTERSECTION_LENGTH {
        return false;
    }

    let dehomogenized = binary_dehomogenize_t_one(polynomial);
    let dehom_degree = univariate_degree(&dehomogenized);
    if dehom_degree + 1 < polynomial.degree() {
        return false;
    }

    let derivative = univariate_derivative(&dehomogenized);
    univariate_gcd(dehomogenized, derivative).len() == 1
}

fn binary_dehomogenize_t_one<const P: i64>(polynomial: &BinaryPolynomialFp<P>) -> Vec<Fp<P>> {
    let degree = polynomial.degree();
    let mut coefficients = vec![Fp::<P>::zero(); degree + 1];
    for term in polynomial.terms() {
        coefficients[term.exponents()[0]] = coefficients[term.exponents()[0]] + term.coefficient();
    }
    trim_univariate(coefficients)
}

fn count_binary_projective_roots<const P: i64>(polynomial: &BinaryPolynomialFp<P>) -> usize {
    projective_points_p1_mod_p::<P>()
        .into_iter()
        .filter(|point| polynomial.evaluate(point).is_zero())
        .count()
}

fn scan_plane_quartic_events<const P: i64>(
    reflection_label: &'static str,
    quotient: &TernaryPolynomialFp<P>,
    node_orbit_size: usize,
    contact_orbit_size: usize,
) -> PlaneQuarticEventScan {
    let off_axis_nodes = projective_points_p2_mod_p::<P>()
        .into_iter()
        .filter(|point| point.iter().all(|coord| !coord.is_zero()))
        .filter(|point| quotient_node_at(quotient, point))
        .count();
    let z_axis_contacts = quotient_axis_contacts_mod_p(quotient, SegreCoordinateAxis::Z);
    let w_axis_contacts = quotient_axis_contacts_mod_p(quotient, SegreCoordinateAxis::W);
    let linear_factors = count_projective_linear_factors(quotient);

    PlaneQuarticEventScan {
        reflection_label,
        off_axis_nodes,
        z_axis_contacts,
        w_axis_contacts,
        linear_factors,
        node_orbit_size,
        contact_orbit_size,
    }
}

fn quotient_node_at<const P: i64>(quotient: &TernaryPolynomialFp<P>, point: &[Fp<P>; 3]) -> bool {
    quotient.evaluate(point).is_zero()
        && (0..3).all(|variable| {
            quotient
                .partial_derivative(variable)
                .evaluate(point)
                .is_zero()
        })
        && ternary_hessian_rank_fp(quotient, point) == 2
}

fn quotient_axis_contacts_mod_p<const P: i64>(
    quotient: &TernaryPolynomialFp<P>,
    axis: SegreCoordinateAxis,
) -> usize {
    let (restriction, lift) = restrict_quotient_to_axis_fp(quotient, axis);
    projective_points_p1_mod_p::<P>()
        .into_iter()
        .filter(|binary_point| binary_point.iter().all(|coord| !coord.is_zero()))
        .filter(|binary_point| {
            restriction.evaluate(binary_point).is_zero()
                && (0..2).all(|variable| {
                    restriction
                        .partial_derivative(variable)
                        .evaluate(binary_point)
                        .is_zero()
                })
                && {
                    let point = lift(*binary_point);
                    !point[0].is_zero()
                }
        })
        .count()
}

fn restrict_quotient_to_axis_fp<const P: i64>(
    quotient: &TernaryPolynomialFp<P>,
    axis: SegreCoordinateAxis,
) -> AxisRestrictionFp<P> {
    let [s, t] = binary_variables_fp();
    let zero = BinaryPolynomialFp::<P>::zero();
    let (forms, lift): ([BinaryPolynomialFp<P>; 3], AxisLiftFp<P>) = match axis {
        SegreCoordinateAxis::Z => ([s, zero, t], |point| [point[0], Fp::zero(), point[1]]),
        SegreCoordinateAxis::W => ([s, t, zero], |point| [point[0], point[1], Fp::zero()]),
    };

    (
        quotient
            .terms()
            .into_iter()
            .fold(BinaryPolynomialFp::<P>::zero(), |sum, term| {
                let substituted = term.exponents().into_iter().enumerate().fold(
                    BinaryPolynomialFp::<P>::constant(term.coefficient()),
                    |product, (variable, exponent)| {
                        product.mul(&forms[variable].pow_usize(exponent))
                    },
                );
                sum.add(&substituted)
            }),
        lift,
    )
}

fn count_projective_linear_factors<const P: i64>(quotient: &TernaryPolynomialFp<P>) -> usize {
    let points = projective_points_p2_mod_p::<P>();
    projective_points_p2_mod_p::<P>()
        .into_iter()
        .filter(|line| {
            let mut point_count = 0;
            let all_zero = points
                .iter()
                .filter(|point| line_eval_p2(line, point).is_zero())
                .inspect(|_| point_count += 1)
                .all(|point| quotient.evaluate(point).is_zero());
            all_zero && point_count == (P + 1) as usize
        })
        .count()
}

fn line_eval_p2<const P: i64>(line: &[Fp<P>; 3], point: &[Fp<P>; 3]) -> Fp<P> {
    line.iter()
        .zip(point)
        .fold(Fp::zero(), |sum, (coefficient, coord)| {
            sum + *coefficient * *coord
        })
}

fn ternary_hessian_rank_fp<const P: i64>(
    polynomial: &TernaryPolynomialFp<P>,
    point: &[Fp<P>; 3],
) -> usize {
    Matrix::from_rows(
        (0..3)
            .map(|row| {
                let first = polynomial.partial_derivative(row);
                (0..3)
                    .map(|col| first.partial_derivative(col).evaluate(point))
                    .collect()
            })
            .collect(),
    )
    .rank()
}

fn reduce_q2_polynomial_mod_p<const P: i64>(
    polynomial: &PolynomialP3,
    sqrt2: Fp<P>,
) -> PolynomialP3Fp<P> {
    polynomial.map_coefficients(|coefficient| q2_mod_p(*coefficient, sqrt2))
}

fn q2_mod_p<const P: i64>(value: Q2, sqrt2: Fp<P>) -> Fp<P> {
    let rational = rational_mod_p(value.rational());
    let irrational = rational_mod_p(value.irrational());
    match value.radicand() {
        0 => rational,
        2 => rational + irrational * sqrt2,
        radicand => panic!("cannot reduce sqrt({radicand}) with only sqrt(2) data"),
    }
}

fn rational_mod_p<const P: i64>(value: Rational) -> Fp<P> {
    fp_i128_mod_p::<P>(value.numerator()) / fp_i128_mod_p::<P>(value.denominator())
}

fn fp_i128_mod_p<const P: i64>(value: i128) -> Fp<P> {
    Fp::new(value.rem_euclid(P.into()) as i64)
}

fn projective_points_p2_mod_p<const P: i64>() -> Vec<[Fp<P>; 3]> {
    let mut points = Vec::new();
    for first_nonzero in 0..3 {
        let free_count = 3 - first_nonzero - 1;
        let mut suffix = vec![0; free_count];
        loop {
            let mut coords = [Fp::<P>::zero(); 3];
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

fn projective_points_p1_mod_p<const P: i64>() -> Vec<[Fp<P>; 2]> {
    let mut points = (0..P)
        .map(|value| [Fp::one(), Fp::new(value)])
        .collect::<Vec<_>>();
    points.push([Fp::zero(), Fp::one()]);
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

fn extended_gcd_i64(lhs: i64, rhs: i64) -> (i64, i64, i64) {
    if rhs == 0 {
        return (lhs.abs(), lhs.signum(), 0);
    }
    let (gcd, x, y) = extended_gcd_i64(rhs, lhs.rem_euclid(rhs));
    (gcd, y, x - (lhs / rhs) * y)
}

fn trim_univariate<const P: i64>(mut polynomial: Vec<Fp<P>>) -> Vec<Fp<P>> {
    while polynomial.len() > 1 && polynomial.last().is_some_and(FieldElement::is_zero) {
        polynomial.pop();
    }
    if polynomial.is_empty() {
        polynomial.push(Fp::zero());
    }
    polynomial
}

fn univariate_degree<const P: i64>(polynomial: &[Fp<P>]) -> usize {
    polynomial
        .iter()
        .rposition(|coefficient| !coefficient.is_zero())
        .unwrap_or(0)
}

fn univariate_derivative<const P: i64>(polynomial: &[Fp<P>]) -> Vec<Fp<P>> {
    if polynomial.len() <= 1 {
        return vec![Fp::zero()];
    }
    trim_univariate(
        polynomial
            .iter()
            .enumerate()
            .skip(1)
            .map(|(exponent, coefficient)| *coefficient * Fp::new(exponent as i64))
            .collect(),
    )
}

fn univariate_gcd<const P: i64>(mut lhs: Vec<Fp<P>>, mut rhs: Vec<Fp<P>>) -> Vec<Fp<P>> {
    lhs = trim_univariate(lhs);
    rhs = trim_univariate(rhs);
    while !univariate_is_zero(&rhs) {
        let remainder = univariate_remainder(lhs, rhs.clone());
        lhs = rhs;
        rhs = remainder;
    }
    univariate_monic(lhs)
}

fn univariate_remainder<const P: i64>(mut lhs: Vec<Fp<P>>, rhs: Vec<Fp<P>>) -> Vec<Fp<P>> {
    let rhs = trim_univariate(rhs);
    assert!(
        !univariate_is_zero(&rhs),
        "cannot divide by zero polynomial"
    );
    lhs = trim_univariate(lhs);

    while !univariate_is_zero(&lhs) && univariate_degree(&lhs) >= univariate_degree(&rhs) {
        let lhs_degree = univariate_degree(&lhs);
        let rhs_degree = univariate_degree(&rhs);
        let degree_delta = lhs_degree - rhs_degree;
        let factor = lhs[lhs_degree] / rhs[rhs_degree];
        for (index, coefficient) in rhs.iter().enumerate() {
            lhs[index + degree_delta] = lhs[index + degree_delta] - factor * *coefficient;
        }
        lhs = trim_univariate(lhs);
    }

    lhs
}

fn univariate_monic<const P: i64>(polynomial: Vec<Fp<P>>) -> Vec<Fp<P>> {
    let polynomial = trim_univariate(polynomial);
    if univariate_is_zero(&polynomial) {
        return polynomial;
    }
    let leading = polynomial[univariate_degree(&polynomial)];
    polynomial
        .into_iter()
        .map(|coefficient| coefficient / leading)
        .collect()
}

fn univariate_is_zero<const P: i64>(polynomial: &[Fp<P>]) -> bool {
    polynomial.iter().all(FieldElement::is_zero)
}

fn substitute_p3(
    polynomial: &PolynomialP3,
    forms: &[PolynomialP3; P3_VARIABLE_COUNT],
) -> PolynomialP3 {
    polynomial
        .terms()
        .into_iter()
        .fold(PolynomialP3::zero(), |sum, term| {
            let substituted = term.exponents().into_iter().enumerate().fold(
                PolynomialP3::constant(term.coefficient()),
                |product, (variable, exponent)| product.mul(&forms[variable].pow_usize(exponent)),
            );
            sum.add(&substituted)
        })
}

fn restrict_p3_to_line(
    polynomial: &PolynomialP3,
    basis: [[Q2; P3_VARIABLE_COUNT]; 2],
) -> BinaryPolynomial {
    let [s, t] = binary_variables();
    let forms: [BinaryPolynomial; P3_VARIABLE_COUNT] = std::array::from_fn(|variable| {
        s.scale(basis[0][variable])
            .add(&t.scale(basis[1][variable]))
    });

    polynomial
        .terms()
        .into_iter()
        .fold(BinaryPolynomial::zero(), |sum, term| {
            let substituted = term.exponents().into_iter().enumerate().fold(
                BinaryPolynomial::constant(term.coefficient()),
                |product, (variable, exponent)| product.mul(&forms[variable].pow_usize(exponent)),
            );
            sum.add(&substituted)
        })
}

fn verify_endrass_segre_event(event: EndrassExtraNodeEvent) -> EndrassSegreEventVerification {
    let quotient = endrass_segre_quotient(event.reflection_plane());
    let point = event.segre_point();
    let quotient_value_zero = quotient.evaluate(&point).is_zero();
    let quotient_gradient_zero = (0..3).all(|variable| {
        quotient
            .partial_derivative(variable)
            .evaluate(&point)
            .is_zero()
    });
    let quotient_hessian_rank = ternary_hessian_rank(&quotient, &point);
    let contact_axis = segre_contact_axis(event.label());
    let axis_contact = contact_axis
        .map(|axis| quotient_axis_contact(&quotient, &point, axis))
        .unwrap_or(false);
    let (lift_singular, lift_hessian_rank) = verify_lifted_event(event);

    EndrassSegreEventVerification {
        label: event.label(),
        kind: event.kind(),
        quotient_value_zero,
        quotient_gradient_zero,
        quotient_hessian_rank,
        contact_axis,
        axis_contact,
        lift_singular,
        lift_hessian_rank,
    }
}

fn restrict_octic_to_reflection_plane(plane: EndrassReflectionPlane) -> TernaryPolynomial {
    let [u, z, w] = ternary_variables();
    let forms = match plane {
        EndrassReflectionPlane::E0 => [u, TernaryPolynomial::zero(), z, w],
        EndrassReflectionPlane::E1 => {
            let y = u;
            [y.scale(q(1) + sqrt2()), y, z, w]
        }
    };
    substitute_p3_to_ternary(&endrass_octic_polynomial(), &forms)
}

fn substitute_p3_to_ternary(
    polynomial: &PolynomialP3,
    forms: &[TernaryPolynomial; P3_VARIABLE_COUNT],
) -> TernaryPolynomial {
    polynomial
        .terms()
        .into_iter()
        .fold(TernaryPolynomial::zero(), |sum, term| {
            let substituted = term.exponents().into_iter().enumerate().fold(
                TernaryPolynomial::constant(term.coefficient()),
                |product, (variable, exponent)| product.mul(&forms[variable].pow_usize(exponent)),
            );
            sum.add(&substituted)
        })
}

fn substitute_p3_to_ternary_fp<const P: i64>(
    polynomial: &PolynomialP3Fp<P>,
    forms: &[TernaryPolynomialFp<P>; P3_VARIABLE_COUNT],
) -> TernaryPolynomialFp<P> {
    polynomial
        .terms()
        .into_iter()
        .fold(TernaryPolynomialFp::<P>::zero(), |sum, term| {
            let substituted = term.exponents().into_iter().enumerate().fold(
                TernaryPolynomialFp::<P>::constant(term.coefficient()),
                |product, (variable, exponent)| product.mul(&forms[variable].pow_usize(exponent)),
            );
            sum.add(&substituted)
        })
}

fn segre_quotient_from_even_ternary(polynomial: &TernaryPolynomial) -> TernaryPolynomial {
    TernaryPolynomial::from_terms(
        polynomial
            .terms()
            .into_iter()
            .map(|term| {
                let exponents = term.exponents();
                assert!(
                    exponents.iter().all(|exponent| exponent % 2 == 0),
                    "Segre quotient expects an even polynomial"
                );
                (
                    term.coefficient(),
                    std::array::from_fn(|index| exponents[index] / 2),
                )
            })
            .collect(),
    )
}

fn segre_quotient_from_even_ternary_fp<const P: i64>(
    polynomial: &TernaryPolynomialFp<P>,
) -> TernaryPolynomialFp<P> {
    TernaryPolynomialFp::<P>::from_terms(
        polynomial
            .terms()
            .into_iter()
            .map(|term| {
                let exponents = term.exponents();
                assert!(
                    exponents.iter().all(|exponent| exponent % 2 == 0),
                    "finite-field Segre quotient expects an even polynomial"
                );
                (
                    term.coefficient(),
                    std::array::from_fn(|index| exponents[index] / 2),
                )
            })
            .collect(),
    )
}

fn ternary_hessian_rank(polynomial: &TernaryPolynomial, point: &[Q2; 3]) -> usize {
    Matrix::from_rows(
        (0..3)
            .map(|row| {
                let first = polynomial.partial_derivative(row);
                (0..3)
                    .map(|col| first.partial_derivative(col).evaluate(point))
                    .collect()
            })
            .collect(),
    )
    .rank()
}

fn segre_contact_axis(label: &str) -> Option<SegreCoordinateAxis> {
    match label {
        "t3" | "v2" => Some(SegreCoordinateAxis::Z),
        "v1" => Some(SegreCoordinateAxis::W),
        _ => None,
    }
}

fn quotient_axis_contact(
    quotient: &TernaryPolynomial,
    point: &[Q2; 3],
    axis: SegreCoordinateAxis,
) -> bool {
    let (restriction, binary_point) = restrict_quotient_to_axis(quotient, point, axis);
    restriction.evaluate(&binary_point).is_zero()
        && (0..2).all(|variable| {
            restriction
                .partial_derivative(variable)
                .evaluate(&binary_point)
                .is_zero()
        })
}

fn restrict_quotient_to_axis(
    quotient: &TernaryPolynomial,
    point: &[Q2; 3],
    axis: SegreCoordinateAxis,
) -> (BinaryPolynomial, [Q2; 2]) {
    let [s, t] = binary_variables();
    let zero = BinaryPolynomial::zero();
    let (forms, binary_point) = match axis {
        SegreCoordinateAxis::Z => ([s, zero, t], [point[0], point[2]]),
        SegreCoordinateAxis::W => ([s, t, zero], [point[0], point[1]]),
    };
    (
        quotient
            .terms()
            .into_iter()
            .fold(BinaryPolynomial::zero(), |sum, term| {
                let substituted = term.exponents().into_iter().enumerate().fold(
                    BinaryPolynomial::constant(term.coefficient()),
                    |product, (variable, exponent)| {
                        product.mul(&forms[variable].pow_usize(exponent))
                    },
                );
                sum.add(&substituted)
            }),
        binary_point,
    )
}

fn verify_lifted_event(event: EndrassExtraNodeEvent) -> (bool, usize) {
    if event.label() == "s3" {
        return verify_s3_lift_over_nested_q2(event);
    }

    let point = lift_point_q2(event);
    let polynomial = endrass_octic();
    let coords = point.p3_coords();
    let singular = polynomial.polynomial().evaluate(&coords).is_zero()
        && polynomial
            .polynomial()
            .gradient_at(&coords)
            .into_iter()
            .all(|value| value.is_zero());
    let hessian_rank = polynomial.polynomial().hessian_at(&coords).rank();
    (singular, hessian_rank)
}

fn verify_s3_lift_over_nested_q2(event: EndrassExtraNodeEvent) -> (bool, usize) {
    let [u, v, w] = event.segre_point();
    assert_eq!(v, q(1), "s3 lift assumes z=1");
    assert_eq!(w, q(4), "s3 lift assumes w=2");

    let polynomial = HomogeneousPolynomialP3::from(
        endrass_octic_polynomial().map_coefficients(|coefficient| NestedQ2::from_q2(*coefficient)),
    );
    let coords = [
        NestedQ2::sqrt(u),
        NestedQ2::zero(),
        NestedQ2::one(),
        NestedQ2::from_q2(q(2)),
    ];
    let singular = polynomial.evaluate(&coords).is_zero()
        && polynomial
            .gradient_at(&coords)
            .into_iter()
            .all(|value| value.is_zero());
    let hessian_rank = polynomial.hessian_at(&coords).rank();
    (singular, hessian_rank)
}

fn lift_point_q2(event: EndrassExtraNodeEvent) -> nodal_core::ProjectivePoint<Q2> {
    let coords = match event.label() {
        "t3" => [q(1), q(0), q(0), sqrt2()],
        "u5" => {
            let y = q(2) - sqrt2();
            let z = sqrt2() - q(1);
            [(q(1) + sqrt2()) * y, y, z, q(2)]
        }
        "v1" => [q(1) + sqrt2(), q(1), q(1) + sqrt2(), q(0)],
        "v2" => [q(1) + sqrt2(), q(1), q(0), q(2)],
        label => panic!("no Q(sqrt2) lift recorded for {label}"),
    };
    nodal_core::ProjectivePoint::new(coords.into_iter().collect())
}

fn ternary_variables() -> [TernaryPolynomial; 3] {
    std::array::from_fn(TernaryPolynomial::variable)
}

fn vec_to_p3(vector: Vec<Q2>) -> [Q2; P3_VARIABLE_COUNT] {
    assert_eq!(vector.len(), P3_VARIABLE_COUNT);
    [vector[0], vector[1], vector[2], vector[3]]
}

pub fn plane_evaluates_on_vector(plane: EndrassPlane, vector: &[Q2; P3_VARIABLE_COUNT]) -> Q2 {
    plane
        .coefficients()
        .into_iter()
        .zip(vector)
        .fold(q(0), |sum, (coefficient, value)| sum + coefficient * *value)
}

fn q(value: i64) -> Q2 {
    Q2::from_i64(value)
}

fn qr(numerator: i64, denominator: i64) -> Q2 {
    Q2::from_rational(Rational::new(numerator.into(), denominator.into()))
}

fn qsqrt(numerator: i64, denominator: i64) -> Q2 {
    Q2::new(
        Rational::ZERO,
        Rational::new(numerator.into(), denominator.into()),
        2,
    )
}

fn sqrt2() -> Q2 {
    Q2::sqrt(2)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn endrass_octic_has_degree_eight_over_sqrt_two() {
        let surface = endrass_octic();

        assert_eq!(surface.polynomial().degree(), ENDRASS_DEGREE);
        assert!(endrass_octic_polynomial().is_homogeneous());
    }

    #[test]
    fn plane_product_matches_four_quadratic_factors() {
        assert_eq!(
            endrass_plane_product_polynomial(),
            endrass_quadratic_factor_product_polynomial()
        );
        assert_eq!(endrass_plane_product_polynomial().degree(), 8);
    }

    #[test]
    fn final_octic_has_d8_times_z2_symmetry() {
        let polynomial = endrass_octic_polynomial();

        assert_eq!(rotation_45_pullback(&polynomial), polynomial);
        assert_eq!(y_reflection_pullback(&polynomial), polynomial);
        assert_eq!(z_reflection_pullback(&polynomial), polynomial);
    }

    #[test]
    fn eight_planes_and_twenty_eight_lines_are_well_formed() {
        let planes = endrass_planes();
        let lines = endrass_intersection_lines();

        assert_eq!(planes.len(), ENDRASS_PLANE_COUNT);
        assert_eq!(lines.len(), ENDRASS_INTERSECTION_LINE_COUNT);

        for line in lines {
            let (first, second) = line.planes();
            for basis_vector in line.basis() {
                assert!(plane_evaluates_on_vector(endrass_plane(first), &basis_vector).is_zero());
                assert!(plane_evaluates_on_vector(endrass_plane(second), &basis_vector).is_zero());
            }
        }
    }

    #[test]
    fn quartic_restrictions_give_the_basic_112_node_skeleton() {
        for line in endrass_intersection_lines() {
            let restriction = line.quartic_restriction();
            assert!(!restriction.is_zero(), "{:?}", line.planes());
            assert_eq!(
                restriction.degree(),
                ENDRASS_BASIC_LINE_INTERSECTION_LENGTH,
                "{:?}",
                line.planes()
            );
        }

        assert_eq!(
            endrass_basic_node_count_from_line_structure(),
            ENDRASS_BASIC_NODE_COUNT
        );
    }

    #[test]
    fn line_orbit_representatives_account_for_the_basic_nodes() {
        let candidates = endrass_basic_node_orbit_candidates();
        let separations = candidates
            .iter()
            .map(|candidate| candidate.separation())
            .collect::<Vec<_>>();

        assert_eq!(separations, vec![1, 2, 3, 4]);
        assert_eq!(
            candidates
                .iter()
                .map(|candidate| candidate.line_orbit_size())
                .collect::<Vec<_>>(),
            vec![8, 8, 8, 4]
        );
        assert_eq!(
            endrass_basic_node_count_from_orbits(),
            ENDRASS_BASIC_NODE_COUNT
        );
    }

    #[test]
    fn segre_plane_events_account_for_the_extra_56_nodes() {
        let events = endrass_extra_node_events();
        let labels = events.iter().map(|event| event.label()).collect::<Vec<_>>();

        assert_eq!(labels, vec!["s3", "t3", "u5", "v1", "v2"]);
        assert_eq!(
            events
                .iter()
                .map(|event| event.surface_orbit_size())
                .collect::<Vec<_>>(),
            vec![16, 8, 16, 8, 8]
        );
        assert!(
            events
                .iter()
                .all(|event| event.segre_point().iter().any(|coord| !coord.is_zero()))
        );
        assert_eq!(
            endrass_extra_node_count_from_segre_events(),
            ENDRASS_EXTRA_NODE_COUNT
        );
    }

    #[test]
    fn segre_quotient_verifier_checks_the_extra_events() {
        let verifications = verify_endrass_segre_events();

        assert_eq!(verifications.len(), 5);
        for verification in &verifications {
            assert!(
                verification.verified(),
                "{} should verify: {:?}",
                verification.label(),
                verification
            );
        }

        let quotient_e0 = endrass_segre_quotient(EndrassReflectionPlane::E0);
        let quotient_e1 = endrass_segre_quotient(EndrassReflectionPlane::E1);
        assert_eq!(quotient_e0.degree(), 4);
        assert_eq!(quotient_e1.degree(), 4);
    }

    #[test]
    fn structural_count_and_bounds_match_endrass_claim() {
        let structural_count = endrass_structural_node_count();
        let miyaoka_bound = miyaoka_node_bound(8);

        assert_eq!(structural_count, ENDRASS_TOTAL_NODE_COUNT);
        assert_eq!(miyaoka_bound, ENDRASS_MIYAOKA_UPPER_BOUND);
        assert_eq!(
            varchenko_arnold_number_degree8(),
            ENDRASS_VARCHENKO_DEGREE8_BOUND
        );
        assert!(structural_count < miyaoka_bound);
    }

    #[test]
    fn finite_field_scorer_recognizes_endrass_mod_31() {
        let stats = endrass_finite_field_stats_mod_31();

        assert_eq!(stats.total_sing(), ENDRASS_TOTAL_NODE_COUNT);
        assert_eq!(stats.node_like(), ENDRASS_TOTAL_NODE_COUNT);
        assert_eq!(stats.bad_sing(), 0);
        assert_eq!(stats.base_like(), ENDRASS_BASIC_NODE_COUNT);
        assert_eq!(stats.extra_like(), ENDRASS_EXTRA_NODE_COUNT);
        assert_eq!(stats.line_profile().len(), ENDRASS_INTERSECTION_LINE_COUNT);
        assert_eq!(
            stats.line_profile().iter().sum::<usize>(),
            ENDRASS_BASIC_NODE_COUNT
        );
        assert_eq!(
            stats
                .orbit_profile()
                .iter()
                .map(|(size, count)| size * count)
                .sum::<usize>(),
            ENDRASS_TOTAL_NODE_COUNT
        );
    }

    #[test]
    fn basic_line_length_scorer_tracks_visible_roots_separately() {
        let mod31 = score_basic_line_lengths(&FiniteFieldScorerInput::<31>::endrass(8));
        let mod73 = score_basic_line_lengths(&FiniteFieldScorerInput::<73>::endrass(32));

        assert!(mod31.all_lines_degree_four_squarefree());
        assert_eq!(mod31.triple_plane_bad_points(), 0);
        assert_eq!(mod31.algebraic_closure_length(), ENDRASS_BASIC_NODE_COUNT);
        assert_eq!(mod31.visible_root_count(), ENDRASS_BASIC_NODE_COUNT);

        assert!(mod73.all_lines_degree_four_squarefree());
        assert_eq!(mod73.triple_plane_bad_points(), 0);
        assert_eq!(mod73.algebraic_closure_length(), ENDRASS_BASIC_NODE_COUNT);
        assert!(
            mod73.visible_root_count() < mod73.algebraic_closure_length(),
            "p=73 keeps the algebraic length but not every line root is F_p-visible"
        );
    }

    #[test]
    fn endrass_multi_prime_calibration_keeps_the_base_scheme_stable() {
        let calibrations = endrass_multi_prime_calibrations();

        let table = calibrations
            .iter()
            .map(|calibration| {
                (
                    calibration.prime(),
                    calibration.sqrt2(),
                    calibration.global_visible_nodes(),
                    calibration.global_bad_singularities(),
                    calibration.base_algebraic_closure_length(),
                    calibration.base_visible_roots(),
                    calibration.segre_event_orbit_contribution(),
                )
            })
            .collect::<Vec<_>>();

        assert_eq!(
            table,
            vec![
                (31, 8, 168, 0, 112, 112, 168),
                (41, 17, 168, 0, 112, 112, 168),
                (73, 32, 144, 0, 112, 104, 168),
                (89, 25, 144, 0, 112, 104, 168),
            ]
        );
        assert!(
            calibrations
                .iter()
                .all(
                    |calibration| calibration.sqrt2() * calibration.sqrt2() % calibration.prime()
                        == 2
                )
        );
        assert_eq!(
            calibrations
                .iter()
                .map(EndrassPrimeCalibration::prime)
                .collect::<Vec<_>>(),
            vec![31, 41, 73, 89]
        );
        assert_eq!(
            calibrations
                .iter()
                .map(EndrassPrimeCalibration::sqrt2)
                .collect::<Vec<_>>(),
            vec![8, 17, 32, 25]
        );
        assert!(
            calibrations
                .iter()
                .all(|calibration| calibration.base_algebraic_closure_length()
                    == ENDRASS_BASIC_NODE_COUNT)
        );
        assert_eq!(
            calibrations[0].global_visible_nodes(),
            ENDRASS_TOTAL_NODE_COUNT
        );
        assert_eq!(
            calibrations[1].global_visible_nodes(),
            ENDRASS_TOTAL_NODE_COUNT
        );
        assert!(
            calibrations[2].global_visible_nodes() < ENDRASS_TOTAL_NODE_COUNT,
            "larger primes need not make every Endrass node F_p-visible"
        );
        assert!(
            calibrations
                .iter()
                .all(|calibration| calibration.global_bad_singularities() == 0)
        );
    }

    #[test]
    fn d4_reflection_event_orbit_sizes_match_the_scanner_weights() {
        let symmetry = search_core::SurfaceSymmetry::<31>::D4TimesZ2;
        let generic_reflection_event = [Fp::<31>::new(1), Fp::zero(), Fp::new(2), Fp::new(3)];
        let z_axis_contact = [Fp::<31>::new(1), Fp::zero(), Fp::zero(), Fp::new(3)];
        let w_axis_contact = [Fp::<31>::new(1), Fp::zero(), Fp::new(2), Fp::zero()];

        assert_eq!(
            search_core::symmetry_orbit_points(&symmetry, generic_reflection_event).len(),
            8
        );
        assert_eq!(
            search_core::symmetry_orbit_points(&symmetry, z_axis_contact).len(),
            4
        );
        assert_eq!(
            search_core::symmetry_orbit_points(&symmetry, w_axis_contact).len(),
            4
        );
    }

    #[test]
    fn d4_event_scanner_and_candidate_records_are_sortable() {
        let parameters = endrass_parameters_mod_p::<31>(8);
        let candidate = scan_d4_candidate(parameters);

        assert_eq!(
            candidate.singularity_stats().node_like(),
            ENDRASS_TOTAL_NODE_COUNT
        );
        assert_eq!(
            candidate.base_length_stats().algebraic_closure_length(),
            ENDRASS_BASIC_NODE_COUNT
        );
        assert_eq!(candidate.event_scans().len(), 2);
        assert!(
            candidate
                .event_scans()
                .iter()
                .all(|scan| scan.predicted_orbit_contribution() > 0)
        );

        let local = scan_d4_local_window(parameters, 0, 1);
        assert_eq!(local.len(), 1);
        assert_eq!(local[0].parameters(), parameters);
        assert!(D4SearchCandidate::<31>::tsv_header().contains("prime"));
        assert!(local[0].to_tsv().contains("axis-y0"));
    }

    #[test]
    fn d4_linear_event_enumerator_finds_endrass_satisfied_events() {
        let parameters = endrass_parameters_mod_p::<31>(8);
        let events = enumerate_d4_linear_events(parameters);
        assert!(
            events
                .iter()
                .any(|event| event.kind() == D4EventKind::ZAxisContact)
        );
        let satisfied = events
            .into_iter()
            .filter(|&event| d4_event_constraints_hold(parameters, event))
            .collect::<Vec<_>>();

        assert!(
            satisfied
                .iter()
                .any(|event| event.kind() == D4EventKind::OffAxisNode)
        );
        assert!(
            satisfied
                .iter()
                .any(|event| event.kind() == D4EventKind::ZAxisContact)
        );
        assert!(satisfied.len() >= 4);
    }

    #[test]
    fn d4_linear_event_solver_recovers_endrass_from_seed_events() {
        let parameters = endrass_parameters_mod_p::<31>(8);
        let events = enumerate_d4_linear_events(parameters)
            .into_iter()
            .filter(|&event| d4_event_constraints_hold(parameters, event))
            .collect::<Vec<_>>();
        let expected = d4_r_coefficients(parameters);

        let rows = d4_linear_event_rows(parameters, &events);
        let solution = solve_d4_affine_linear_system(&rows)
            .expect("Endrass-satisfied event equations should be consistent");
        let recovered = enumerate_affine_solutions(&solution)
            .into_iter()
            .any(|coefficients| coefficients == expected);

        assert!(
            recovered,
            "the Endrass R coefficients should lie in the nonzero-rho event solution space"
        );
    }

    #[test]
    fn d4_event_candidate_records_include_seed_events_and_json() {
        let parameters = endrass_parameters_mod_p::<31>(8);
        let seed_event = enumerate_d4_linear_events(parameters)
            .into_iter()
            .find(|&event| d4_event_constraints_hold(parameters, event))
            .expect("Endrass reduction should satisfy at least one nonzero-rho event");
        let generated = D4GeneratedCandidate {
            seed_events: vec![seed_event],
            free_dimension: 1,
            candidate: scan_d4_candidate(parameters),
        };

        assert!(D4GeneratedCandidate::<31>::tsv_header().contains("seed_events"));
        assert!(!generated.seed_events().is_empty());
        assert_eq!(
            generated
                .candidate()
                .base_length_stats()
                .algebraic_closure_length(),
            ENDRASS_BASIC_NODE_COUNT
        );
        assert!(generated.to_tsv().contains("axis"));
        assert!(generated.to_json_line().contains("\"seed_events\""));
    }

    #[test]
    fn d4_family_can_specialize_to_the_endrass_mod_31_point() {
        let endrass = FiniteFieldScorerInput::<31>::endrass(8);
        let d4 = FiniteFieldScorerInput::<31>::d4_family(endrass_parameters_mod_p(8));

        assert_eq!(d4.polynomial, endrass.polynomial);
        assert_eq!(d4.quartic_r, endrass.quartic_r);
    }
}
