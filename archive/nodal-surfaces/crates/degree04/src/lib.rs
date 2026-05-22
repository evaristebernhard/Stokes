use nodal_core::{HomogeneousPolynomialP3, Matrix, ProjectivePoint, QuadraticRational, Rational};
use std::collections::BTreeMap;
use std::fmt;

type Q2 = QuadraticRational;

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct QuarticSurface {
    polynomial: HomogeneousPolynomialP3<Q2>,
}

impl QuarticSurface {
    pub fn new(polynomial: HomogeneousPolynomialP3<Q2>) -> Self {
        assert_eq!(polynomial.degree(), 4, "expected a quartic surface");
        Self { polynomial }
    }

    pub fn polynomial(&self) -> &HomogeneousPolynomialP3<Q2> {
        &self.polynomial
    }

    pub fn verify_node(&self, point: ProjectivePoint<Q2>) -> NodeVerification {
        let coords = point.p3_coords();
        let value = self.polynomial.evaluate(&coords);
        let gradient = self.polynomial.gradient_at(&coords);
        let hessian = self.polynomial.hessian_at(&coords);
        let hessian_rank = hessian.rank();

        NodeVerification {
            point,
            value,
            gradient,
            hessian_rank,
            ordinary_double_point: value.is_zero()
                && gradient.into_iter().all(Q2::is_zero)
                && hessian_rank == 3,
            hessian,
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct NodeVerification {
    point: ProjectivePoint<Q2>,
    value: Q2,
    gradient: [Q2; 4],
    hessian_rank: usize,
    ordinary_double_point: bool,
    hessian: Matrix<Q2>,
}

impl NodeVerification {
    pub fn point(&self) -> &ProjectivePoint<Q2> {
        &self.point
    }

    pub fn value(&self) -> Q2 {
        self.value
    }

    pub fn gradient(&self) -> [Q2; 4] {
        self.gradient
    }

    pub fn hessian_rank(&self) -> usize {
        self.hessian_rank
    }

    pub fn ordinary_double_point(&self) -> bool {
        self.ordinary_double_point
    }

    pub fn hessian(&self) -> &Matrix<Q2> {
        &self.hessian
    }
}

impl fmt::Display for NodeVerification {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}: F = {}, gradient = [{}, {}, {}, {}], Hessian rank = {}, ordinary node = {}",
            self.point,
            self.value,
            self.gradient[0],
            self.gradient[1],
            self.gradient[2],
            self.gradient[3],
            self.hessian_rank,
            self.ordinary_double_point
        )
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum AffineGradientCase {
    CoordinateAxis,
    XZeroYNonzero,
    YZeroXNonzero,
    BothNonzero,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum AffineZCoordinate {
    Rational(Rational),
    SquareRootPair { square: Rational },
}

impl AffineZCoordinate {
    pub fn point_count(self) -> usize {
        match self {
            Self::Rational(_) => 1,
            Self::SquareRootPair { .. } => 2,
        }
    }

    fn rational(self) -> Option<Rational> {
        match self {
            Self::Rational(value) => Some(value),
            Self::SquareRootPair { .. } => None,
        }
    }

    fn square(self) -> Rational {
        match self {
            Self::Rational(value) => value * value,
            Self::SquareRootPair { square } => square,
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct AffineGradientBranch {
    case: AffineGradientCase,
    x_squared: Rational,
    y_squared: Rational,
    z: AffineZCoordinate,
    point_count: usize,
    surface_value: Rational,
}

impl AffineGradientBranch {
    pub fn case(&self) -> AffineGradientCase {
        self.case
    }

    pub fn x_squared(&self) -> Rational {
        self.x_squared
    }

    pub fn y_squared(&self) -> Rational {
        self.y_squared
    }

    pub fn z(&self) -> AffineZCoordinate {
        self.z
    }

    pub fn point_count(&self) -> usize {
        self.point_count
    }

    pub fn surface_point_count(&self) -> usize {
        if self.surface_value.is_zero() {
            self.point_count
        } else {
            0
        }
    }

    pub fn surface_value(&self) -> Rational {
        self.surface_value
    }

    pub fn computed_surface_value(&self) -> Rational {
        match self.z.rational() {
            Some(z) => affine_surface_value(self.x_squared, self.y_squared, z),
            None => {
                debug_assert!(self.x_squared.is_zero());
                debug_assert!(self.y_squared.is_zero());
                let z_squared = self.z.square();
                -rq(16) * z_squared * z_squared + rq(20) * z_squared - rq(1)
            }
        }
    }

    pub fn gradient_equations_hold(&self) -> bool {
        match (self.case, self.z.rational()) {
            (AffineGradientCase::CoordinateAxis, Some(z)) => {
                self.x_squared.is_zero()
                    && self.y_squared.is_zero()
                    && (z * (-rq(8) * z * z + rq(5))).is_zero()
            }
            (AffineGradientCase::CoordinateAxis, None) => {
                self.x_squared.is_zero()
                    && self.y_squared.is_zero()
                    && (-rq(8) * self.z.square() + rq(5)).is_zero()
            }
            (AffineGradientCase::XZeroYNonzero, Some(z)) => {
                self.x_squared.is_zero()
                    && !self.y_squared.is_zero()
                    && affine_factor_b(self.x_squared, self.y_squared, z).is_zero()
                    && affine_factor_c(self.x_squared, self.y_squared, z).is_zero()
            }
            (AffineGradientCase::YZeroXNonzero, Some(z)) => {
                self.y_squared.is_zero()
                    && !self.x_squared.is_zero()
                    && affine_factor_a(self.x_squared, self.y_squared, z).is_zero()
                    && affine_factor_c(self.x_squared, self.y_squared, z).is_zero()
            }
            (AffineGradientCase::BothNonzero, Some(z)) => {
                !self.x_squared.is_zero()
                    && !self.y_squared.is_zero()
                    && affine_factor_a(self.x_squared, self.y_squared, z).is_zero()
                    && affine_factor_b(self.x_squared, self.y_squared, z).is_zero()
                    && affine_factor_c(self.x_squared, self.y_squared, z).is_zero()
            }
            _ => false,
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct InfinityChartCertificate {
    all_nonzero_rank: usize,
    coordinate_zero_case_ranks: [usize; 3],
    no_singular_points: bool,
}

impl InfinityChartCertificate {
    pub fn all_nonzero_rank(&self) -> usize {
        self.all_nonzero_rank
    }

    pub fn coordinate_zero_case_ranks(&self) -> [usize; 3] {
        self.coordinate_zero_case_ranks
    }

    pub fn no_singular_points(&self) -> bool {
        self.no_singular_points
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Trope {
    plane: [Q2; 4],
    section: DoubleConicCertificate,
}

impl Trope {
    pub fn plane(&self) -> [Q2; 4] {
        self.plane
    }

    pub fn contains(&self, point: &ProjectivePoint<Q2>) -> bool {
        self.plane_value_at(&point.p3_coords()).is_zero()
    }

    pub fn plane_value_at(&self, coords: &[Q2; 4]) -> Q2 {
        self.plane
            .iter()
            .zip(coords)
            .fold(q(0), |sum, (&coefficient, &coord)| {
                sum + coefficient * coord
            })
    }

    pub fn verifies_double_conic(&self, surface: &QuarticSurface) -> bool {
        self.section.verify(surface.polynomial(), &self.plane)
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct DoubleConicCertificate {
    solve_variable: usize,
    scalar: Q2,
    conic_terms: Vec<(Q2, [usize; 3])>,
}

impl DoubleConicCertificate {
    pub fn solve_variable(&self) -> usize {
        self.solve_variable
    }

    pub fn scalar(&self) -> Q2 {
        self.scalar
    }

    fn verify(&self, polynomial: &HomogeneousPolynomialP3<Q2>, plane: &[Q2; 4]) -> bool {
        let restricted = restrict_to_plane(polynomial, plane, self.solve_variable);
        let conic = TernaryPolynomial::from_terms(self.conic_terms.clone());
        let expected = conic.mul(&conic).scale(self.scalar);

        restricted == expected
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TropeVerification {
    trope_index: usize,
    incident_node_indices: Vec<usize>,
    double_conic: bool,
}

impl TropeVerification {
    pub fn trope_index(&self) -> usize {
        self.trope_index
    }

    pub fn incident_node_indices(&self) -> &[usize] {
        &self.incident_node_indices
    }

    pub fn double_conic(&self) -> bool {
        self.double_conic
    }
}

pub fn kummer_quartic() -> QuarticSurface {
    // Variable order is [x:y:z:w]. This is a rational scalar multiple of
    // (x^2+y^2+z^2-3/2*w^2)^2
    //   - 7/3 * (((w-z)^2-2x^2) * ((w+z)^2-2y^2)).
    QuarticSurface::new(HomogeneousPolynomialP3::from_terms(vec![
        (q(12), [4, 0, 0, 0]),
        (q(-88), [2, 2, 0, 0]),
        (q(80), [2, 0, 2, 0]),
        (q(112), [2, 0, 1, 1]),
        (q(20), [2, 0, 0, 2]),
        (q(12), [0, 4, 0, 0]),
        (q(80), [0, 2, 2, 0]),
        (q(-112), [0, 2, 1, 1]),
        (q(20), [0, 2, 0, 2]),
        (q(-16), [0, 0, 4, 0]),
        (q(20), [0, 0, 2, 2]),
        (q(-1), [0, 0, 0, 4]),
    ]))
}

pub fn kummer_nodes() -> Vec<ProjectivePoint<Q2>> {
    let mut nodes = Vec::new();

    for sign in [-1, 1] {
        nodes.push(p3_point([q(0), s2(sign, 2), q(1), q(1)]));
        nodes.push(p3_point([q(0), s2(sign, 4), r(1, 4), q(1)]));
        nodes.push(p3_point([s2(sign, 2), q(0), q(-1), q(1)]));
        nodes.push(p3_point([s2(sign, 4), q(0), r(-1, 4), q(1)]));
    }

    for x_sign in [-1, 1] {
        for y_sign in [-1, 1] {
            nodes.push(p3_point([s2(3 * x_sign, 4), s2(y_sign, 4), r(-1, 2), q(1)]));
            nodes.push(p3_point([s2(x_sign, 4), s2(3 * y_sign, 4), r(1, 2), q(1)]));
        }
    }

    nodes
}

pub fn affine_gradient_branches() -> Vec<AffineGradientBranch> {
    use AffineGradientCase::{BothNonzero, CoordinateAxis, XZeroYNonzero, YZeroXNonzero};

    vec![
        affine_branch(CoordinateAxis, (0, 1), (0, 1), z_rat(0, 1), 1, (-1, 1)),
        affine_branch(
            CoordinateAxis,
            (0, 1),
            (0, 1),
            z_square_pair(5, 8),
            2,
            (21, 4),
        ),
        affine_branch(XZeroYNonzero, (0, 1), (1, 8), z_rat(1, 4), 2, (0, 1)),
        affine_branch(XZeroYNonzero, (0, 1), (1, 2), z_rat(1, 1), 2, (0, 1)),
        affine_branch(XZeroYNonzero, (0, 1), (25, 32), z_rat(5, 8), 2, (-189, 64)),
        affine_branch(YZeroXNonzero, (1, 8), (0, 1), z_rat(-1, 4), 2, (0, 1)),
        affine_branch(YZeroXNonzero, (1, 2), (0, 1), z_rat(-1, 1), 2, (0, 1)),
        affine_branch(YZeroXNonzero, (25, 32), (0, 1), z_rat(-5, 8), 2, (-189, 64)),
        affine_branch(BothNonzero, (1, 8), (9, 8), z_rat(1, 2), 4, (0, 1)),
        affine_branch(BothNonzero, (5, 16), (5, 16), z_rat(0, 1), 4, (21, 4)),
        affine_branch(BothNonzero, (9, 8), (1, 8), z_rat(-1, 2), 4, (0, 1)),
    ]
}

pub fn affine_gradient_candidate_count() -> usize {
    affine_gradient_branches()
        .iter()
        .map(AffineGradientBranch::point_count)
        .sum()
}

pub fn affine_surface_singular_candidate_count() -> usize {
    affine_gradient_branches()
        .iter()
        .map(AffineGradientBranch::surface_point_count)
        .sum()
}

pub fn affine_surface_singular_points() -> Vec<ProjectivePoint<Q2>> {
    let mut points = Vec::new();

    for branch in affine_gradient_branches()
        .into_iter()
        .filter(|branch| branch.surface_value().is_zero())
    {
        let z = branch
            .z()
            .rational()
            .expect("surface branches of this certificate have rational z");

        for x_value in sqrt_q2_values(branch.x_squared()) {
            for y_value in sqrt_q2_values(branch.y_squared()) {
                points.push(p3_point([x_value, y_value, Q2::from_rational(z), q(1)]));
            }
        }
    }

    points
}

pub fn infinity_chart_certificate() -> InfinityChartCertificate {
    let all_nonzero = Matrix::<Rational>::from_rows(vec![
        vec![rq(3), rq(-11), rq(10)],
        vec![rq(11), rq(-3), rq(-10)],
        vec![rq(5), rq(5), rq(-2)],
    ]);
    let x_zero = Matrix::<Rational>::from_rows(vec![vec![rq(-3), rq(-10)], vec![rq(5), rq(-2)]]);
    let y_zero = Matrix::<Rational>::from_rows(vec![vec![rq(3), rq(10)], vec![rq(5), rq(-2)]]);
    let z_zero = Matrix::<Rational>::from_rows(vec![vec![rq(3), rq(-11)], vec![rq(11), rq(-3)]]);
    let coordinate_zero_case_ranks = [x_zero.rank(), y_zero.rank(), z_zero.rank()];
    let all_nonzero_rank = all_nonzero.rank();

    InfinityChartCertificate {
        all_nonzero_rank,
        coordinate_zero_case_ranks,
        no_singular_points: all_nonzero_rank == 3
            && coordinate_zero_case_ranks.into_iter().all(|rank| rank == 2),
    }
}

pub fn kummer_tropes() -> Vec<Trope> {
    vec![
        trope(
            [q(1), q(-3), s2(-1, 1), s2(-1, 2)],
            section(
                0,
                q(192),
                conic_terms(s2(2, 1), s2(1, 1), q(1), r(5, 4), r(1, 4)),
            ),
        ),
        trope(
            [q(1), q(3), s2(1, 1), s2(1, 2)],
            section(
                0,
                q(192),
                conic_terms(s2(2, 1), s2(1, 1), q(1), r(5, 4), r(1, 4)),
            ),
        ),
        trope(
            [q(1), r(-1, 3), s2(-1, 3), s2(1, 6)],
            section(
                0,
                r(64, 27),
                conic_terms(s2(-4, 1), s2(2, 1), q(-1), r(-5, 4), r(-1, 4)),
            ),
        ),
        trope(
            [q(1), q(0), s2(-1, 2), s2(1, 2)],
            section(0, q(12), conic_terms(q(0), q(0), r(3, 2), q(-1), q(-1))),
        ),
        trope(
            [q(1), q(0), s2(1, 2), s2(-1, 2)],
            section(0, q(12), conic_terms(q(0), q(0), r(3, 2), q(-1), q(-1))),
        ),
        trope(
            [q(1), r(1, 3), s2(1, 3), s2(-1, 6)],
            section(
                0,
                r(64, 27),
                conic_terms(s2(-4, 1), s2(2, 1), q(-1), r(-5, 4), r(-1, 4)),
            ),
        ),
        trope(
            [q(1), r(1, 3), s2(-1, 3), s2(1, 6)],
            section(
                0,
                r(64, 27),
                conic_terms(s2(4, 1), s2(-2, 1), q(-1), r(-5, 4), r(-1, 4)),
            ),
        ),
        trope(
            [q(1), r(-1, 3), s2(1, 3), s2(-1, 6)],
            section(
                0,
                r(64, 27),
                conic_terms(s2(4, 1), s2(-2, 1), q(-1), r(-5, 4), r(-1, 4)),
            ),
        ),
        trope(
            [q(1), q(0), s2(-1, 1), s2(1, 4)],
            section(0, q(12), conic_terms(q(0), q(0), q(-4), q(-1), r(3, 8))),
        ),
        trope(
            [q(1), q(0), s2(1, 1), s2(-1, 4)],
            section(0, q(12), conic_terms(q(0), q(0), q(-4), q(-1), r(3, 8))),
        ),
        trope(
            [q(1), q(3), s2(-1, 1), s2(-1, 2)],
            section(
                0,
                q(192),
                conic_terms(s2(-2, 1), s2(-1, 1), q(1), r(5, 4), r(1, 4)),
            ),
        ),
        trope(
            [q(0), q(1), s2(1, 2), s2(1, 2)],
            section(1, q(12), conic_terms(q(0), q(0), r(3, 2), q(1), q(-1))),
        ),
        trope(
            [q(0), q(1), s2(-1, 2), s2(-1, 2)],
            section(1, q(12), conic_terms(q(0), q(0), r(3, 2), q(1), q(-1))),
        ),
        trope(
            [q(1), q(-3), s2(1, 1), s2(1, 2)],
            section(
                0,
                q(192),
                conic_terms(s2(-2, 1), s2(-1, 1), q(1), r(5, 4), r(1, 4)),
            ),
        ),
        trope(
            [q(0), q(1), s2(-1, 1), s2(-1, 4)],
            section(1, q(12), conic_terms(q(0), q(0), q(-4), q(1), r(3, 8))),
        ),
        trope(
            [q(0), q(1), s2(1, 1), s2(1, 4)],
            section(1, q(12), conic_terms(q(0), q(0), q(-4), q(1), r(3, 8))),
        ),
    ]
}

pub fn kummer_trope_verifications() -> Vec<TropeVerification> {
    let surface = kummer_quartic();
    let nodes = kummer_nodes();

    kummer_tropes()
        .into_iter()
        .enumerate()
        .map(|(trope_index, trope)| {
            let incident_node_indices = nodes
                .iter()
                .enumerate()
                .filter_map(|(node_index, node)| trope.contains(node).then_some(node_index))
                .collect();
            let double_conic = trope.verifies_double_conic(&surface);

            TropeVerification {
                trope_index,
                incident_node_indices,
                double_conic,
            }
        })
        .collect()
}

pub fn kummer_incidence_matrix() -> Vec<Vec<bool>> {
    let nodes = kummer_nodes();

    kummer_tropes()
        .into_iter()
        .map(|trope| nodes.iter().map(|node| trope.contains(node)).collect())
        .collect()
}

pub fn kummer_node_verifications() -> Vec<NodeVerification> {
    let surface = kummer_quartic();
    kummer_nodes()
        .into_iter()
        .map(|point| surface.verify_node(point))
        .collect()
}

pub fn kummer_node_count() -> usize {
    kummer_nodes().len()
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct TernaryPolynomial {
    terms: BTreeMap<[usize; 3], Q2>,
}

impl TernaryPolynomial {
    fn zero() -> Self {
        Self {
            terms: BTreeMap::new(),
        }
    }

    fn constant(coefficient: Q2) -> Self {
        Self::from_terms(vec![(coefficient, [0, 0, 0])])
    }

    fn variable(variable: usize) -> Self {
        assert!(variable < 3, "ternary variable index out of range");
        let mut exponents = [0, 0, 0];
        exponents[variable] = 1;

        Self::from_terms(vec![(q(1), exponents)])
    }

    fn linear_form(coefficients: [Q2; 3]) -> Self {
        Self::from_terms(
            coefficients
                .into_iter()
                .enumerate()
                .map(|(variable, coefficient)| {
                    let mut exponents = [0, 0, 0];
                    exponents[variable] = 1;
                    (coefficient, exponents)
                })
                .collect(),
        )
    }

    fn from_terms(terms: Vec<(Q2, [usize; 3])>) -> Self {
        let mut combined = BTreeMap::<[usize; 3], Q2>::new();

        for (coefficient, exponents) in terms {
            if coefficient.is_zero() {
                continue;
            }
            let entry = combined.entry(exponents).or_insert(q(0));
            *entry = *entry + coefficient;
        }

        combined.retain(|_, coefficient| !coefficient.is_zero());

        Self { terms: combined }
    }

    fn add(&self, rhs: &Self) -> Self {
        let mut terms: Vec<_> = self
            .terms
            .iter()
            .map(|(&exponents, &coefficient)| (coefficient, exponents))
            .collect();
        terms.extend(
            rhs.terms
                .iter()
                .map(|(&exponents, &coefficient)| (coefficient, exponents)),
        );

        Self::from_terms(terms)
    }

    fn mul(&self, rhs: &Self) -> Self {
        let mut terms = Vec::new();

        for (&left_exponents, &left_coefficient) in &self.terms {
            for (&right_exponents, &right_coefficient) in &rhs.terms {
                let exponents =
                    std::array::from_fn(|index| left_exponents[index] + right_exponents[index]);
                terms.push((left_coefficient * right_coefficient, exponents));
            }
        }

        Self::from_terms(terms)
    }

    fn scale(&self, scalar: Q2) -> Self {
        Self::from_terms(
            self.terms
                .iter()
                .map(|(&exponents, &coefficient)| (scalar * coefficient, exponents))
                .collect(),
        )
    }

    fn pow_usize(&self, exponent: usize) -> Self {
        (0..exponent).fold(Self::constant(q(1)), |value, _| value.mul(self))
    }
}

fn restrict_to_plane(
    polynomial: &HomogeneousPolynomialP3<Q2>,
    plane: &[Q2; 4],
    solve_variable: usize,
) -> TernaryPolynomial {
    assert!(solve_variable < 4, "P3 variable index out of range");
    assert!(
        !plane[solve_variable].is_zero(),
        "cannot solve a plane for a variable with zero coefficient"
    );

    let remaining_variables: Vec<_> = (0..4)
        .filter(|&variable| variable != solve_variable)
        .collect();
    let solved_coefficients =
        std::array::from_fn(|index| -plane[remaining_variables[index]] / plane[solve_variable]);
    let solved_polynomial = TernaryPolynomial::linear_form(solved_coefficients);
    let coordinate_polynomials: Vec<_> = (0..4)
        .map(|variable| {
            if variable == solve_variable {
                solved_polynomial.clone()
            } else {
                let ternary_variable = remaining_variables
                    .iter()
                    .position(|&remaining| remaining == variable)
                    .expect("unsolved variable must occur in remaining list");
                TernaryPolynomial::variable(ternary_variable)
            }
        })
        .collect();

    let mut result = TernaryPolynomial::zero();
    for term in polynomial.terms() {
        let mut monomial = TernaryPolynomial::constant((*term).coefficient());
        let exponents = (*term).exponents();
        for (variable, &exponent) in exponents.iter().enumerate() {
            monomial = monomial.mul(&coordinate_polynomials[variable].pow_usize(exponent));
        }
        result = result.add(&monomial);
    }

    result
}

fn affine_branch(
    case: AffineGradientCase,
    x_squared: (i64, i64),
    y_squared: (i64, i64),
    z: AffineZCoordinate,
    point_count: usize,
    surface_value: (i64, i64),
) -> AffineGradientBranch {
    AffineGradientBranch {
        case,
        x_squared: rat(x_squared.0, x_squared.1),
        y_squared: rat(y_squared.0, y_squared.1),
        z,
        point_count,
        surface_value: rat(surface_value.0, surface_value.1),
    }
}

fn affine_factor_a(x_squared: Rational, y_squared: Rational, z: Rational) -> Rational {
    rq(6) * x_squared - rq(22) * y_squared + rq(20) * z * z + rq(28) * z + rq(5)
}

fn affine_factor_b(x_squared: Rational, y_squared: Rational, z: Rational) -> Rational {
    rq(22) * x_squared - rq(6) * y_squared - rq(20) * z * z + rq(28) * z - rq(5)
}

fn affine_factor_c(x_squared: Rational, y_squared: Rational, z: Rational) -> Rational {
    (rq(20) * z + rq(14)) * x_squared + (rq(20) * z - rq(14)) * y_squared - rq(8) * z * z * z
        + rq(5) * z
}

fn affine_surface_value(x_squared: Rational, y_squared: Rational, z: Rational) -> Rational {
    rq(12) * x_squared * x_squared - rq(88) * x_squared * y_squared
        + rq(80) * x_squared * z * z
        + rq(112) * x_squared * z
        + rq(20) * x_squared
        + rq(12) * y_squared * y_squared
        + rq(80) * y_squared * z * z
        - rq(112) * y_squared * z
        + rq(20) * y_squared
        - rq(16) * z * z * z * z
        + rq(20) * z * z
        - rq(1)
}

fn trope(plane: [Q2; 4], section: DoubleConicCertificate) -> Trope {
    Trope { plane, section }
}

fn section(
    solve_variable: usize,
    scalar: Q2,
    conic_terms: Vec<(Q2, [usize; 3])>,
) -> DoubleConicCertificate {
    DoubleConicCertificate {
        solve_variable,
        scalar,
        conic_terms,
    }
}

fn conic_terms(
    variable_z: Q2,
    variable_w: Q2,
    z_squared: Q2,
    z_w: Q2,
    w_squared: Q2,
) -> Vec<(Q2, [usize; 3])> {
    vec![
        (q(1), [2, 0, 0]),
        (variable_z, [1, 1, 0]),
        (variable_w, [1, 0, 1]),
        (z_squared, [0, 2, 0]),
        (z_w, [0, 1, 1]),
        (w_squared, [0, 0, 2]),
    ]
    .into_iter()
    .filter(|(coefficient, _)| !coefficient.is_zero())
    .collect()
}

fn sqrt_q2_values(square: Rational) -> Vec<Q2> {
    if square.is_zero() {
        return vec![q(0)];
    }

    let positive_root = if square == rat(1, 8) {
        s2(1, 4)
    } else if square == rat(1, 2) {
        s2(1, 2)
    } else if square == rat(9, 8) {
        s2(3, 4)
    } else {
        panic!("unsupported square in Q(sqrt(2)) surface branch: {square}");
    };

    vec![-positive_root, positive_root]
}

fn z_rat(numerator: i64, denominator: i64) -> AffineZCoordinate {
    AffineZCoordinate::Rational(rat(numerator, denominator))
}

fn z_square_pair(numerator: i64, denominator: i64) -> AffineZCoordinate {
    AffineZCoordinate::SquareRootPair {
        square: rat(numerator, denominator),
    }
}

fn rq(value: i64) -> Rational {
    Rational::from_i64(value)
}

fn rat(numerator: i64, denominator: i64) -> Rational {
    Rational::new(numerator.into(), denominator.into())
}

fn q(value: i64) -> Q2 {
    Q2::from_i64(value)
}

fn r(numerator: i64, denominator: i64) -> Q2 {
    Q2::from_rational(rat(numerator, denominator))
}

fn s2(numerator: i64, denominator: i64) -> Q2 {
    Q2::new(
        Rational::ZERO,
        Rational::new(numerator.into(), denominator.into()),
        2,
    )
}

fn p3_point(coords: [Q2; 4]) -> ProjectivePoint<Q2> {
    ProjectivePoint::new(coords.into_iter().collect())
}

#[cfg(test)]
mod tests {
    use super::{
        affine_gradient_branches, affine_gradient_candidate_count,
        affine_surface_singular_candidate_count, affine_surface_singular_points,
        infinity_chart_certificate, kummer_incidence_matrix, kummer_node_count,
        kummer_node_verifications, kummer_nodes, kummer_quartic, kummer_trope_verifications,
        kummer_tropes, q,
    };

    #[test]
    fn kummer_quartic_has_degree_four() {
        let surface = kummer_quartic();

        assert_eq!(surface.polynomial().degree(), 4);
        assert_eq!(surface.polynomial().terms().len(), 12);
    }

    #[test]
    fn kummer_certificate_lists_sixteen_nodes() {
        let nodes = kummer_nodes();

        assert_eq!(kummer_node_count(), 16);
        assert_eq!(nodes.len(), 16);
    }

    #[test]
    fn listed_points_are_ordinary_double_points() {
        for verification in kummer_node_verifications() {
            assert_eq!(verification.value(), q(0));
            assert_eq!(verification.gradient(), [q(0); 4]);
            assert_eq!(verification.hessian_rank(), 3);
            assert!(verification.ordinary_double_point());
        }
    }

    #[test]
    fn affine_chart_certificate_exhausts_surface_singularities() {
        for branch in affine_gradient_branches() {
            assert!(branch.gradient_equations_hold());
            assert_eq!(branch.surface_value(), branch.computed_surface_value());
        }

        assert_eq!(affine_gradient_candidate_count(), 27);
        assert_eq!(affine_surface_singular_candidate_count(), 16);
        assert_eq!(
            point_keys(affine_surface_singular_points()),
            point_keys(kummer_nodes())
        );
    }

    #[test]
    fn infinity_chart_certificate_rules_out_singular_points() {
        let certificate = infinity_chart_certificate();

        assert_eq!(certificate.all_nonzero_rank(), 3);
        assert_eq!(certificate.coordinate_zero_case_ranks(), [2, 2, 2]);
        assert!(certificate.no_singular_points());
    }

    #[test]
    fn kummer_tropes_have_classic_sixteen_six_incidence() {
        let tropes = kummer_tropes();
        let incidence = kummer_incidence_matrix();

        assert_eq!(tropes.len(), 16);
        let mut plane_keys: Vec<_> = tropes
            .iter()
            .map(|trope| {
                trope
                    .plane()
                    .iter()
                    .map(ToString::to_string)
                    .collect::<Vec<_>>()
                    .join("|")
            })
            .collect();
        plane_keys.sort();
        plane_keys.dedup();
        assert_eq!(plane_keys.len(), 16);

        assert_eq!(incidence.len(), 16);
        for row in &incidence {
            assert_eq!(row.len(), 16);
            assert_eq!(row.iter().filter(|&&incident| incident).count(), 6);
        }

        for node_index in 0..16 {
            assert_eq!(incidence.iter().filter(|row| row[node_index]).count(), 6);
        }

        for verification in kummer_trope_verifications() {
            assert_eq!(verification.incident_node_indices().len(), 6);
            assert!(verification.double_conic());
        }
    }

    #[test]
    fn a_general_point_is_not_singular() {
        let surface = kummer_quartic();
        let point = super::p3_point([q(1), q(1), q(1), q(1)]);

        assert!(!surface.polynomial().is_singular_at(&point));
        assert!(!surface.polynomial().is_ordinary_double_point_at(&point));
    }

    fn point_keys(points: Vec<super::ProjectivePoint<super::Q2>>) -> Vec<String> {
        let mut keys: Vec<_> = points.into_iter().map(|point| point.to_string()).collect();
        keys.sort();
        keys
    }
}
