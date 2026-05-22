use nodal_core::{
    FieldElement, HomogeneousPolynomialP3, Matrix, P3_VARIABLE_COUNT, QuadraticRational, Rational,
    SparsePolynomial,
};
use std::collections::{BTreeMap, BTreeSet, VecDeque};
use std::ops::{Add, Div, Mul, Neg, Sub};

type Q2 = QuadraticRational;
type PolynomialP3 = SparsePolynomial<Q2, P3_VARIABLE_COUNT>;
type BinaryPolynomial = SparsePolynomial<Q2, 2>;
type TernaryPolynomial = SparsePolynomial<Q2, 3>;

pub const ENDRASS_DEGREE: usize = 8;
pub const ENDRASS_PLANE_COUNT: usize = 8;
pub const ENDRASS_INTERSECTION_LINE_COUNT: usize = 28;
pub const ENDRASS_BASIC_LINE_INTERSECTION_LENGTH: usize = 4;
pub const ENDRASS_BASIC_NODE_COUNT: usize = 112;
pub const ENDRASS_EXTRA_NODE_COUNT: usize = 56;
pub const ENDRASS_TOTAL_NODE_COUNT: usize = 168;
pub const ENDRASS_MIYAOKA_UPPER_BOUND: usize = 174;
pub const ENDRASS_VARCHENKO_DEGREE8_BOUND: usize = 180;

type PolynomialP3Fp<const P: i64> = SparsePolynomial<Fp<P>, P3_VARIABLE_COUNT>;

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
    let surface = FiniteFieldSurface::new(input.polynomial.clone());
    let line_pairs = plane_line_pairs(input.planes.len());
    let mut line_profile = vec![0; line_pairs.len()];
    let mut singular_points = Vec::new();

    for coords in projective_points_mod_p::<P>() {
        if !surface.is_singular_at(&coords) {
            continue;
        }

        let hessian_rank = surface.hessian_rank_at(&coords);
        let incident_planes = incident_planes(&input.planes, &coords);
        let incident_lines = incident_line_pairs(&incident_planes);
        let base_like = hessian_rank == 3
            && !incident_lines.is_empty()
            && input.quartic_r.evaluate(&coords).is_zero();

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
    let node_like_points: Vec<_> = singular_points
        .iter()
        .filter(|point| point.hessian_rank == 3)
        .map(|point| point.coords)
        .collect();
    let node_like = node_like_points.len();
    let base_like = singular_points
        .iter()
        .filter(|point| point.hessian_rank == 3 && point.base_like)
        .count();
    let orbit_profile = orbit_profile(input, &node_like_points);

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
    let [x, y, z, w] = variables_fp();
    let radius_squared = x.pow_usize(2).add(&y.pow_usize(2));

    radius_squared
        .pow_usize(2)
        .scale(parameters.a)
        .add(&x.pow_usize(2).mul(&y.pow_usize(2)).scale(parameters.h))
        .add(
            &radius_squared.mul(
                &z.pow_usize(2)
                    .scale(parameters.b)
                    .add(&w.pow_usize(2).scale(parameters.d)),
            ),
        )
        .add(&z.pow_usize(4).scale(parameters.e))
        .add(&z.pow_usize(2).mul(&w.pow_usize(2)).scale(parameters.g))
        .add(&w.pow_usize(4).scale(parameters.i))
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

struct FiniteFieldSurface<const P: i64> {
    polynomial: PolynomialP3Fp<P>,
    gradient: [PolynomialP3Fp<P>; P3_VARIABLE_COUNT],
    hessian: [[PolynomialP3Fp<P>; P3_VARIABLE_COUNT]; P3_VARIABLE_COUNT],
}

impl<const P: i64> FiniteFieldSurface<P> {
    fn new(polynomial: PolynomialP3Fp<P>) -> Self {
        let gradient: [PolynomialP3Fp<P>; P3_VARIABLE_COUNT] =
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

    fn is_singular_at(&self, coords: &[Fp<P>; P3_VARIABLE_COUNT]) -> bool {
        self.polynomial.evaluate(coords).is_zero()
            && self
                .gradient
                .iter()
                .all(|partial| partial.evaluate(coords).is_zero())
    }

    fn hessian_rank_at(&self, coords: &[Fp<P>; P3_VARIABLE_COUNT]) -> usize {
        Matrix::from_rows(
            self.hessian
                .iter()
                .map(|row| row.iter().map(|entry| entry.evaluate(coords)).collect())
                .collect(),
        )
        .rank()
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

fn projective_points_mod_p<const P: i64>() -> Vec<[Fp<P>; P3_VARIABLE_COUNT]> {
    let mut points = Vec::new();
    for first_nonzero in 0..P3_VARIABLE_COUNT {
        let free_count = P3_VARIABLE_COUNT - first_nonzero - 1;
        let mut suffix = vec![0; free_count];
        loop {
            let mut coords = [Fp::<P>::zero(); P3_VARIABLE_COUNT];
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

fn incident_planes<const P: i64>(
    planes: &[[Fp<P>; P3_VARIABLE_COUNT]],
    coords: &[Fp<P>; P3_VARIABLE_COUNT],
) -> Vec<usize> {
    planes
        .iter()
        .enumerate()
        .filter_map(|(index, plane)| plane_eval_mod_p(plane, coords).is_zero().then_some(index))
        .collect()
}

fn plane_eval_mod_p<const P: i64>(
    plane: &[Fp<P>; P3_VARIABLE_COUNT],
    coords: &[Fp<P>; P3_VARIABLE_COUNT],
) -> Fp<P> {
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
    input: &FiniteFieldScorerInput<P>,
    node_like_points: &[[Fp<P>; P3_VARIABLE_COUNT]],
) -> BTreeMap<usize, usize> {
    let node_keys: BTreeSet<_> = node_like_points.iter().map(point_key).collect();
    let mut unseen = node_keys.clone();
    let mut profile = BTreeMap::new();

    while let Some(seed) = unseen.iter().next().copied() {
        let seed_point = key_to_point(seed);
        let orbit = symmetry_orbit(input, seed_point);
        let node_orbit: BTreeSet<_> = orbit
            .into_iter()
            .map(|point| point_key(&point))
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
    input: &FiniteFieldScorerInput<P>,
    seed: [Fp<P>; P3_VARIABLE_COUNT],
) -> Vec<[Fp<P>; P3_VARIABLE_COUNT]> {
    let mut seen = BTreeSet::new();
    let mut queue = VecDeque::from([normalize_point(seed)]);

    while let Some(point) = queue.pop_front() {
        if !seen.insert(point_key(&point)) {
            continue;
        }

        for transformed in symmetry_generators(input, &point) {
            let normalized = normalize_point(transformed);
            if !seen.contains(&point_key(&normalized)) {
                queue.push_back(normalized);
            }
        }
    }

    seen.into_iter().map(key_to_point).collect()
}

fn symmetry_generators<const P: i64>(
    input: &FiniteFieldScorerInput<P>,
    point: &[Fp<P>; P3_VARIABLE_COUNT],
) -> Vec<[Fp<P>; P3_VARIABLE_COUNT]> {
    let [x, y, z, w] = *point;
    let z_reflection = [x, y, -z, w];
    match input.symmetry {
        FiniteFieldSymmetry::D4TimesZ2 => vec![[-y, x, z, w], [x, -y, z, w], z_reflection],
        FiniteFieldSymmetry::D8TimesZ2 => {
            let sqrt2 = input.sqrt2.expect("D8 finite-field symmetry needs sqrt(2)");
            let half_sqrt2 = sqrt2 / Fp::new(2);
            vec![
                [(x - y) * half_sqrt2, (x + y) * half_sqrt2, z, w],
                [x, -y, z, w],
                z_reflection,
            ]
        }
    }
}

fn normalize_point<const P: i64>(coords: [Fp<P>; P3_VARIABLE_COUNT]) -> [Fp<P>; P3_VARIABLE_COUNT] {
    let pivot = coords
        .iter()
        .find(|coord| !coord.is_zero())
        .copied()
        .expect("projective point cannot be zero");
    coords.map(|coord| coord / pivot)
}

fn point_key<const P: i64>(coords: &[Fp<P>; P3_VARIABLE_COUNT]) -> [i64; P3_VARIABLE_COUNT] {
    coords.map(Fp::value)
}

fn key_to_point<const P: i64>(key: [i64; P3_VARIABLE_COUNT]) -> [Fp<P>; P3_VARIABLE_COUNT] {
    key.map(Fp::new)
}

fn extended_gcd_i64(lhs: i64, rhs: i64) -> (i64, i64, i64) {
    if rhs == 0 {
        return (lhs.abs(), lhs.signum(), 0);
    }
    let (gcd, x, y) = extended_gcd_i64(rhs, lhs.rem_euclid(rhs));
    (gcd, y, x - (lhs / rhs) * y)
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
        assert_eq!(endrass_structural_node_count(), ENDRASS_TOTAL_NODE_COUNT);
        assert_eq!(miyaoka_node_bound(8), ENDRASS_MIYAOKA_UPPER_BOUND);
        assert_eq!(
            varchenko_arnold_number_degree8(),
            ENDRASS_VARCHENKO_DEGREE8_BOUND
        );
        assert!(ENDRASS_TOTAL_NODE_COUNT < ENDRASS_MIYAOKA_UPPER_BOUND);
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
    fn d4_family_can_specialize_to_the_endrass_mod_31_point() {
        let endrass = FiniteFieldScorerInput::<31>::endrass(8);
        let d4 = FiniteFieldScorerInput::<31>::d4_family(endrass_parameters_mod_p(8));

        assert_eq!(d4.polynomial, endrass.polynomial);
        assert_eq!(d4.quartic_r, endrass.quartic_r);
    }
}
