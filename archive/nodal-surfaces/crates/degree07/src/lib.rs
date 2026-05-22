use nodal_core::{
    AFFINE_P3_VARIABLE_COUNT, BigRational, FieldElement, GroebnerCertificate,
    GroebnerCertificateParseError, GroebnerLiftCertificate, HomogeneousPolynomialP3, MonomialOrder,
    P3_VARIABLE_COUNT, ProjectiveSupport, Rational, SparsePolynomial, p3_affine_variable_indices,
    parse_groebner_lift_certificate,
};
use std::fmt;
use std::ops::{Add, Div, Mul, Neg, Sub};
use std::str::FromStr;

type PolynomialP3 = SparsePolynomial<CubicAlphaRational, P3_VARIABLE_COUNT>;
type PolynomialA3 = SparsePolynomial<CubicAlphaRational, AFFINE_P3_VARIABLE_COUNT>;
type BigPolynomialA3 = SparsePolynomial<BigCubicAlphaRational, AFFINE_P3_VARIABLE_COUNT>;
type PolynomialA4 = SparsePolynomial<CubicAlphaRational, LABS_PROJECTIVE_STRATUM_VARIABLE_COUNT>;
type BigPolynomialA4 =
    SparsePolynomial<BigCubicAlphaRational, LABS_PROJECTIVE_STRATUM_VARIABLE_COUNT>;
pub type LabsProjectiveSupport = ProjectiveSupport<P3_VARIABLE_COUNT>;
pub type LabsGroebnerLiftCertificate<const N: usize> =
    GroebnerLiftCertificate<N, BigCubicAlphaRational>;

pub const LABS_SEPTIC_EXPECTED_NODE_COUNT: usize = 99;
pub const LABS_SEPTIC_PLANE_SECTION_NODE_COUNT: usize = 15;
pub const LABS_SEPTIC_AXIS_PLANE_NODE_COUNT: usize = 1;
pub const LABS_SEPTIC_D7_ORBIT_SIZE: usize = 7;
pub const LABS_PROJECTIVE_SUPPORT_STRATUM_COUNT: usize = (1 << P3_VARIABLE_COUNT) - 1;
pub const LABS_PROJECTIVE_STRATUM_VARIABLE_COUNT: usize = AFFINE_P3_VARIABLE_COUNT + 1;

const LABS_AFFINE_CHART0_GREVLEX_CERTIFICATE: &str =
    include_str!("../certificates/labs-affine-chart0-grevlex.cert");
const LABS_AFFINE_CHART0_HESSIAN_BAD_GREVLEX_CERTIFICATE: &str =
    include_str!("../certificates/labs-affine-chart0-hessian-bad-grevlex.cert");
const LABS_AFFINE_CHART0_SUPPORT15_SATURATION_GREVLEX_CERTIFICATE: &str =
    include_str!("../certificates/labs-affine-chart0-support15-saturation-grevlex.cert");

const LABS_PROJECTIVE_SUPPORT_GREVLEX_CERTIFICATES: [&str; LABS_PROJECTIVE_SUPPORT_STRATUM_COUNT] = [
    include_str!("../certificates/labs-support-01-grevlex.cert"),
    include_str!("../certificates/labs-support-02-grevlex.cert"),
    include_str!("../certificates/labs-support-03-grevlex.cert"),
    include_str!("../certificates/labs-support-04-grevlex.cert"),
    include_str!("../certificates/labs-support-05-grevlex.cert"),
    include_str!("../certificates/labs-support-06-grevlex.cert"),
    include_str!("../certificates/labs-support-07-grevlex.cert"),
    include_str!("../certificates/labs-support-08-grevlex.cert"),
    include_str!("../certificates/labs-support-09-grevlex.cert"),
    include_str!("../certificates/labs-support-10-grevlex.cert"),
    include_str!("../certificates/labs-support-11-grevlex.cert"),
    include_str!("../certificates/labs-support-12-grevlex.cert"),
    include_str!("../certificates/labs-support-13-grevlex.cert"),
    include_str!("../certificates/labs-support-14-grevlex.cert"),
    include_str!("../certificates/labs-support-15-grevlex.cert"),
];

const LABS_PROJECTIVE_SUPPORT_GREVLEX_LIFT_CERTIFICATES: [&str;
    LABS_PROJECTIVE_SUPPORT_STRATUM_COUNT] = [
    include_str!("../certificates/labs-support-01-grevlex.lift"),
    include_str!("../certificates/labs-support-02-grevlex.lift"),
    include_str!("../certificates/labs-support-03-grevlex.lift"),
    include_str!("../certificates/labs-support-04-grevlex.lift"),
    include_str!("../certificates/labs-support-05-grevlex.lift"),
    include_str!("../certificates/labs-support-06-grevlex.lift"),
    include_str!("../certificates/labs-support-07-grevlex.lift"),
    include_str!("../certificates/labs-support-08-grevlex.lift"),
    include_str!("../certificates/labs-support-09-grevlex.lift"),
    include_str!("../certificates/labs-support-10-grevlex.lift"),
    include_str!("../certificates/labs-support-11-grevlex.lift"),
    include_str!("../certificates/labs-support-12-grevlex.lift"),
    include_str!("../certificates/labs-support-13-grevlex.lift"),
    include_str!("../certificates/labs-support-14-grevlex.lift"),
    include_str!("../certificates/labs-support-15-grevlex.lift"),
];

pub const LABS_PROJECTIVE_SUPPORT_STRATUM_LENGTHS: [usize; LABS_PROJECTIVE_SUPPORT_STRATUM_COUNT] =
    [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 14, 0, 0, 0, 84];
pub const LABS_INFINITY_SUPPORT_MASKS: [u8; 7] = [2, 4, 6, 8, 10, 12, 14];
pub const LABS_AFFINE_CHART0_SUPPORT15_SATURATION_LENGTH: usize = 84;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct CubicAlphaRational {
    coefficients: [Rational; 3],
}

impl CubicAlphaRational {
    pub const ZERO: Self = Self {
        coefficients: [Rational::ZERO, Rational::ZERO, Rational::ZERO],
    };
    pub const ONE: Self = Self {
        coefficients: [Rational::ONE, Rational::ZERO, Rational::ZERO],
    };

    pub fn new(constant: Rational, alpha: Rational, alpha_squared: Rational) -> Self {
        Self {
            coefficients: [constant, alpha, alpha_squared],
        }
    }

    pub fn from_i64(value: i64) -> Self {
        Self::from_rational(Rational::from_i64(value))
    }

    pub fn from_rational(value: Rational) -> Self {
        Self::new(value, Rational::ZERO, Rational::ZERO)
    }

    pub fn alpha() -> Self {
        Self::new(Rational::ZERO, Rational::ONE, Rational::ZERO)
    }

    pub fn alpha_squared() -> Self {
        Self::new(Rational::ZERO, Rational::ZERO, Rational::ONE)
    }

    pub fn coefficients(self) -> [Rational; 3] {
        self.coefficients
    }

    pub fn is_zero(self) -> bool {
        self.coefficients
            .iter()
            .all(|coefficient| coefficient.is_zero())
    }

    pub fn inverse(self) -> Self {
        assert!(!self.is_zero(), "cannot invert zero in Q(alpha)");

        let mut matrix = multiplication_matrix(self);
        let mut rhs = [Rational::ONE, Rational::ZERO, Rational::ZERO];

        for pivot_col in 0..3 {
            let pivot_row = (pivot_col..3)
                .find(|&row| !matrix[row][pivot_col].is_zero())
                .expect("nonzero field element has invertible multiplication matrix");
            matrix.swap(pivot_col, pivot_row);
            rhs.swap(pivot_col, pivot_row);

            let pivot = matrix[pivot_col][pivot_col];
            for entry in matrix[pivot_col].iter_mut().skip(pivot_col) {
                *entry = *entry / pivot;
            }
            rhs[pivot_col] = rhs[pivot_col] / pivot;
            let pivot_row_values = matrix[pivot_col];

            for row in 0..3 {
                if row == pivot_col {
                    continue;
                }
                let factor = matrix[row][pivot_col];
                if factor.is_zero() {
                    continue;
                }
                for (entry, pivot_entry) in matrix[row]
                    .iter_mut()
                    .skip(pivot_col)
                    .zip(pivot_row_values.iter().skip(pivot_col))
                {
                    *entry = *entry - factor * *pivot_entry;
                }
                rhs[row] = rhs[row] - factor * rhs[pivot_col];
            }
        }

        Self::new(rhs[0], rhs[1], rhs[2])
    }
}

impl FieldElement for CubicAlphaRational {
    fn zero() -> Self {
        Self::ZERO
    }

    fn one() -> Self {
        Self::ONE
    }

    fn is_zero(&self) -> bool {
        (*self).is_zero()
    }
}

impl From<i64> for CubicAlphaRational {
    fn from(value: i64) -> Self {
        Self::from_i64(value)
    }
}

impl From<Rational> for CubicAlphaRational {
    fn from(value: Rational) -> Self {
        Self::from_rational(value)
    }
}

impl Add for CubicAlphaRational {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        Self::new(
            self.coefficients[0] + rhs.coefficients[0],
            self.coefficients[1] + rhs.coefficients[1],
            self.coefficients[2] + rhs.coefficients[2],
        )
    }
}

impl Sub for CubicAlphaRational {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self::Output {
        self + (-rhs)
    }
}

impl Mul for CubicAlphaRational {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self::Output {
        let mut raw = [Rational::ZERO; 5];
        for lhs_degree in 0..3 {
            for rhs_degree in 0..3 {
                raw[lhs_degree + rhs_degree] = raw[lhs_degree + rhs_degree]
                    + self.coefficients[lhs_degree] * rhs.coefficients[rhs_degree];
            }
        }

        // alpha^3 = -alpha - 1/7 and alpha^4 = -alpha^2 - alpha/7.
        let constant = raw[0] - raw[3] * r(1, 7);
        let alpha = raw[1] - raw[3] - raw[4] * r(1, 7);
        let alpha_squared = raw[2] - raw[4];

        Self::new(constant, alpha, alpha_squared)
    }
}

impl Div for CubicAlphaRational {
    type Output = Self;

    fn div(self, rhs: Self) -> Self::Output {
        Mul::mul(self, rhs.inverse())
    }
}

impl Neg for CubicAlphaRational {
    type Output = Self;

    fn neg(self) -> Self::Output {
        Self::new(
            -self.coefficients[0],
            -self.coefficients[1],
            -self.coefficients[2],
        )
    }
}

impl fmt::Display for CubicAlphaRational {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{} + {}*alpha + {}*alpha^2",
            self.coefficients[0], self.coefficients[1], self.coefficients[2]
        )
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct BigCubicAlphaRational {
    coefficients: [BigRational; 3],
}

impl BigCubicAlphaRational {
    pub fn new(constant: BigRational, alpha: BigRational, alpha_squared: BigRational) -> Self {
        Self {
            coefficients: [constant, alpha, alpha_squared],
        }
    }

    pub fn from_i64(value: i64) -> Self {
        Self::from_rational(BigRational::from_i64(value))
    }

    pub fn from_rational(value: BigRational) -> Self {
        Self::new(value, BigRational::from_i64(0), BigRational::from_i64(0))
    }

    pub fn alpha() -> Self {
        Self::new(
            BigRational::from_i64(0),
            BigRational::from_i64(1),
            BigRational::from_i64(0),
        )
    }

    pub fn alpha_squared() -> Self {
        Self::new(
            BigRational::from_i64(0),
            BigRational::from_i64(0),
            BigRational::from_i64(1),
        )
    }

    pub fn coefficients(&self) -> &[BigRational; 3] {
        &self.coefficients
    }

    pub fn is_zero(&self) -> bool {
        self.coefficients
            .iter()
            .all(|coefficient| coefficient.is_zero())
    }

    pub fn inverse(self) -> Self {
        assert!(!self.is_zero(), "cannot invert zero in Q(alpha)");

        let mut matrix = big_multiplication_matrix(self);
        let mut rhs = [
            BigRational::from_i64(1),
            BigRational::from_i64(0),
            BigRational::from_i64(0),
        ];

        for pivot_col in 0..3 {
            let pivot_row = (pivot_col..3)
                .find(|&row| !matrix[row][pivot_col].is_zero())
                .expect("nonzero field element has invertible multiplication matrix");
            matrix.swap(pivot_col, pivot_row);
            rhs.swap(pivot_col, pivot_row);

            let pivot = matrix[pivot_col][pivot_col].clone();
            for entry in matrix[pivot_col].iter_mut().skip(pivot_col) {
                *entry = entry.clone() / pivot.clone();
            }
            rhs[pivot_col] = rhs[pivot_col].clone() / pivot;
            let pivot_row_values = matrix[pivot_col].clone();

            for row in 0..3 {
                if row == pivot_col {
                    continue;
                }
                let factor = matrix[row][pivot_col].clone();
                if factor.is_zero() {
                    continue;
                }
                for (entry, pivot_entry) in matrix[row]
                    .iter_mut()
                    .skip(pivot_col)
                    .zip(pivot_row_values.iter().skip(pivot_col))
                {
                    *entry = entry.clone() - factor.clone() * pivot_entry.clone();
                }
                rhs[row] = rhs[row].clone() - factor * rhs[pivot_col].clone();
            }
        }

        Self::new(rhs[0].clone(), rhs[1].clone(), rhs[2].clone())
    }
}

impl From<CubicAlphaRational> for BigCubicAlphaRational {
    fn from(value: CubicAlphaRational) -> Self {
        let [constant, alpha, alpha_squared] = value.coefficients();
        Self::new(
            BigRational::from(constant),
            BigRational::from(alpha),
            BigRational::from(alpha_squared),
        )
    }
}

impl From<i64> for BigCubicAlphaRational {
    fn from(value: i64) -> Self {
        Self::from_i64(value)
    }
}

impl FieldElement for BigCubicAlphaRational {
    fn zero() -> Self {
        Self::from_i64(0)
    }

    fn one() -> Self {
        Self::from_i64(1)
    }

    fn is_zero(&self) -> bool {
        self.is_zero()
    }
}

impl Add for BigCubicAlphaRational {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        Self::new(
            self.coefficients[0].clone() + rhs.coefficients[0].clone(),
            self.coefficients[1].clone() + rhs.coefficients[1].clone(),
            self.coefficients[2].clone() + rhs.coefficients[2].clone(),
        )
    }
}

impl Sub for BigCubicAlphaRational {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self::Output {
        self + (-rhs)
    }
}

impl Mul for BigCubicAlphaRational {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self::Output {
        let mut raw = std::array::from_fn::<_, 5, _>(|_| BigRational::from_i64(0));
        for lhs_degree in 0..3 {
            for rhs_degree in 0..3 {
                raw[lhs_degree + rhs_degree] = raw[lhs_degree + rhs_degree].clone()
                    + self.coefficients[lhs_degree].clone() * rhs.coefficients[rhs_degree].clone();
            }
        }

        let seventh = big_r(1, 7);
        let constant = raw[0].clone() - raw[3].clone() * seventh.clone();
        let alpha = raw[1].clone() - raw[3].clone() - raw[4].clone() * seventh;
        let alpha_squared = raw[2].clone() - raw[4].clone();

        Self::new(constant, alpha, alpha_squared)
    }
}

impl Div for BigCubicAlphaRational {
    type Output = Self;

    fn div(self, rhs: Self) -> Self::Output {
        Mul::mul(self, rhs.inverse())
    }
}

impl Neg for BigCubicAlphaRational {
    type Output = Self;

    fn neg(self) -> Self::Output {
        Self::new(
            -self.coefficients[0].clone(),
            -self.coefficients[1].clone(),
            -self.coefficients[2].clone(),
        )
    }
}

impl FromStr for BigCubicAlphaRational {
    type Err = String;

    fn from_str(value: &str) -> Result<Self, Self::Err> {
        parse_big_cubic_alpha_rational(value)
    }
}

impl fmt::Display for BigCubicAlphaRational {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{} + {}*alpha + {}*alpha^2",
            self.coefficients[0], self.coefficients[1], self.coefficients[2]
        )
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SepticSurface {
    polynomial: HomogeneousPolynomialP3<CubicAlphaRational>,
}

impl SepticSurface {
    pub fn new(polynomial: HomogeneousPolynomialP3<CubicAlphaRational>) -> Self {
        assert_eq!(polynomial.degree(), 7, "expected a septic surface");
        Self { polynomial }
    }

    pub fn polynomial(&self) -> &HomogeneousPolynomialP3<CubicAlphaRational> {
        &self.polynomial
    }
}

pub fn labs_septic() -> SepticSurface {
    SepticSurface::new(labs_septic_polynomial())
}

/// Labs's 99-nodal septic in coordinates `[w:x:y:z]`.
pub fn labs_septic_polynomial() -> HomogeneousPolynomialP3<CubicAlphaRational> {
    HomogeneousPolynomialP3::from(labs_septic_sparse_polynomial())
}

pub fn labs_alpha_polynomial_value() -> CubicAlphaRational {
    let alpha = CubicAlphaRational::alpha();
    q(7) * alpha.pow_usize(3) + q(7) * alpha + q(1)
}

pub fn labs_septic_expected_orbit_count_from_plane_section() -> usize {
    LABS_SEPTIC_AXIS_PLANE_NODE_COUNT
        + LABS_SEPTIC_D7_ORBIT_SIZE
            * (LABS_SEPTIC_PLANE_SECTION_NODE_COUNT - LABS_SEPTIC_AXIS_PLANE_NODE_COUNT)
}

pub fn labs_affine_chart_generators(chart_variable: usize) -> Vec<PolynomialA3> {
    labs_septic_polynomial().affine_singular_generators(chart_variable)
}

pub fn labs_affine_chart_variable_indices(
    chart_variable: usize,
) -> [usize; AFFINE_P3_VARIABLE_COUNT] {
    p3_affine_variable_indices(chart_variable)
}

pub fn labs_affine_chart0_grevlex_certificate()
-> Result<LabsAffineChartGroebnerCertificate, GroebnerCertificateParseError> {
    Ok(LabsAffineChartGroebnerCertificate {
        chart_variable: 0,
        certificate: LABS_AFFINE_CHART0_GREVLEX_CERTIFICATE
            .parse::<GroebnerCertificate<AFFINE_P3_VARIABLE_COUNT, BigCubicAlphaRational>>()?,
    })
}

pub fn labs_affine_chart0_hessian_bad_generators() -> Vec<PolynomialA3> {
    let affine_polynomial = labs_septic_polynomial().dehomogenize(0);
    let mut generators = labs_affine_chart_generators(0);
    generators.push(affine_hessian_determinant(&affine_polynomial));
    generators
}

pub fn labs_affine_chart0_hessian_bad_grevlex_certificate()
-> Result<LabsAffineChart0HessianBadGroebnerCertificate, GroebnerCertificateParseError> {
    Ok(LabsAffineChart0HessianBadGroebnerCertificate {
        certificate: LABS_AFFINE_CHART0_HESSIAN_BAD_GREVLEX_CERTIFICATE
            .parse::<GroebnerCertificate<AFFINE_P3_VARIABLE_COUNT, BigCubicAlphaRational>>()?,
    })
}

pub fn labs_affine_chart0_support15_saturation_grevlex_certificate()
-> Result<LabsAffineChart0Support15SaturationGroebnerCertificate, GroebnerCertificateParseError> {
    Ok(LabsAffineChart0Support15SaturationGroebnerCertificate {
        certificate: LABS_AFFINE_CHART0_SUPPORT15_SATURATION_GREVLEX_CERTIFICATE
            .parse::<GroebnerCertificate<AFFINE_P3_VARIABLE_COUNT, BigCubicAlphaRational>>(
        )?,
    })
}

pub fn labs_projective_support_stratum_generators(
    support_mask: u8,
) -> LabsProjectiveSupportStratumGenerators {
    let support = LabsProjectiveSupport::new(support_mask);
    let chart_generators = labs_affine_chart_generators(support.chart_variable());
    let affine_projective_indices = labs_affine_chart_variable_indices(support.chart_variable());
    let mut generators = chart_generators
        .into_iter()
        .map(lift_affine3_polynomial_to_stratum)
        .collect::<Vec<_>>();

    for (affine_variable, &projective_variable) in affine_projective_indices.iter().enumerate() {
        if !support.contains_projective_variable(projective_variable) {
            generators.push(PolynomialA4::variable(affine_variable));
        }
    }

    let mut nonzero_product_exponents = [0; LABS_PROJECTIVE_STRATUM_VARIABLE_COUNT];
    for (affine_variable, &projective_variable) in affine_projective_indices.iter().enumerate() {
        if support.contains_projective_variable(projective_variable) {
            nonzero_product_exponents[affine_variable] = 1;
        }
    }
    nonzero_product_exponents[AFFINE_P3_VARIABLE_COUNT] = 1;
    generators.push(PolynomialA4::from_terms(vec![
        (CubicAlphaRational::ONE, nonzero_product_exponents),
        (
            -CubicAlphaRational::ONE,
            [0; LABS_PROJECTIVE_STRATUM_VARIABLE_COUNT],
        ),
    ]));

    LabsProjectiveSupportStratumGenerators {
        support,
        affine_projective_indices,
        generators,
    }
}

pub fn labs_projective_support_grevlex_certificate(
    support_mask: u8,
) -> Result<LabsProjectiveSupportGroebnerCertificate, GroebnerCertificateParseError> {
    let support = LabsProjectiveSupport::new(support_mask);
    let certificate = LABS_PROJECTIVE_SUPPORT_GREVLEX_CERTIFICATES[usize::from(support_mask - 1)]
        .parse::<GroebnerCertificate<
        LABS_PROJECTIVE_STRATUM_VARIABLE_COUNT,
        BigCubicAlphaRational,
    >>()?;

    Ok(LabsProjectiveSupportGroebnerCertificate {
        support,
        certificate,
    })
}

pub fn labs_projective_support_grevlex_certificates()
-> Result<Vec<LabsProjectiveSupportGroebnerCertificate>, GroebnerCertificateParseError> {
    (1..=LABS_PROJECTIVE_SUPPORT_STRATUM_COUNT)
        .map(|support_mask| labs_projective_support_grevlex_certificate(support_mask as u8))
        .collect()
}

pub fn labs_completed_projective_support_grevlex_certificates()
-> Result<Vec<LabsProjectiveSupportGroebnerCertificate>, GroebnerCertificateParseError> {
    (1..LABS_PROJECTIVE_SUPPORT_STRATUM_COUNT)
        .map(|support_mask| labs_projective_support_grevlex_certificate(support_mask as u8))
        .collect()
}

pub fn labs_infinity_support_grevlex_certificates()
-> Result<Vec<LabsProjectiveSupportGroebnerCertificate>, GroebnerCertificateParseError> {
    LABS_INFINITY_SUPPORT_MASKS
        .into_iter()
        .map(labs_projective_support_grevlex_certificate)
        .collect()
}

pub fn labs_projective_support_grevlex_lift_certificate(
    support_mask: u8,
) -> Result<LabsGroebnerLiftCertificate<LABS_PROJECTIVE_STRATUM_VARIABLE_COUNT>, String> {
    let index = usize::from(support_mask)
        .checked_sub(1)
        .filter(|&index| index < LABS_PROJECTIVE_SUPPORT_STRATUM_COUNT)
        .ok_or_else(|| format!("support mask {support_mask} is out of range"))?;

    parse_groebner_lift_certificate(LABS_PROJECTIVE_SUPPORT_GREVLEX_LIFT_CERTIFICATES[index])
}

pub fn labs_projective_support_grevlex_lift_certificates()
-> Result<Vec<LabsGroebnerLiftCertificate<LABS_PROJECTIVE_STRATUM_VARIABLE_COUNT>>, String> {
    (1..=LABS_PROJECTIVE_SUPPORT_STRATUM_COUNT)
        .map(|support_mask| labs_projective_support_grevlex_lift_certificate(support_mask as u8))
        .collect()
}

pub fn labs_completed_projective_support_grevlex_lift_certificates()
-> Result<Vec<LabsGroebnerLiftCertificate<LABS_PROJECTIVE_STRATUM_VARIABLE_COUNT>>, String> {
    (1..LABS_PROJECTIVE_SUPPORT_STRATUM_COUNT)
        .map(|support_mask| labs_projective_support_grevlex_lift_certificate(support_mask as u8))
        .collect()
}

pub fn labs_infinity_support_grevlex_lift_certificates()
-> Result<Vec<LabsGroebnerLiftCertificate<LABS_PROJECTIVE_STRATUM_VARIABLE_COUNT>>, String> {
    LABS_INFINITY_SUPPORT_MASKS
        .into_iter()
        .map(labs_projective_support_grevlex_lift_certificate)
        .collect()
}

pub fn labs_singular_scheme_certificate() -> Result<LabsSingularSchemeCertificate, String> {
    Ok(LabsSingularSchemeCertificate {
        affine_chart0: labs_affine_chart0_grevlex_certificate()
            .map_err(|error| error.to_string())?,
        hessian_bad: labs_affine_chart0_hessian_bad_grevlex_certificate()
            .map_err(|error| error.to_string())?,
        support15_saturation: labs_affine_chart0_support15_saturation_grevlex_certificate()
            .map_err(|error| error.to_string())?,
        infinity_support_strata: labs_infinity_support_grevlex_certificates()
            .map_err(|error| error.to_string())?,
    })
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct LabsProjectiveSupportStratumGenerators {
    support: LabsProjectiveSupport,
    affine_projective_indices: [usize; AFFINE_P3_VARIABLE_COUNT],
    generators: Vec<PolynomialA4>,
}

impl LabsProjectiveSupportStratumGenerators {
    pub fn support(&self) -> LabsProjectiveSupport {
        self.support
    }

    pub fn chart_variable(&self) -> usize {
        self.support.chart_variable()
    }

    pub fn affine_projective_indices(&self) -> [usize; AFFINE_P3_VARIABLE_COUNT] {
        self.affine_projective_indices
    }

    pub fn generators(&self) -> &[PolynomialA4] {
        &self.generators
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct LabsAffineChartGroebnerCertificate {
    chart_variable: usize,
    certificate: GroebnerCertificate<AFFINE_P3_VARIABLE_COUNT, BigCubicAlphaRational>,
}

impl LabsAffineChartGroebnerCertificate {
    pub fn chart_variable(&self) -> usize {
        self.chart_variable
    }

    pub fn certificate(
        &self,
    ) -> &GroebnerCertificate<AFFINE_P3_VARIABLE_COUNT, BigCubicAlphaRational> {
        &self.certificate
    }

    pub fn expected_generators(&self) -> Vec<BigPolynomialA3> {
        labs_affine_chart_generators(self.chart_variable)
            .into_iter()
            .map(cubic_polynomial_to_big_cubic)
            .collect()
    }

    pub fn generators_match_model(&self) -> bool {
        self.certificate.generators() == self.expected_generators().as_slice()
    }

    pub fn verify(&self) -> LabsAffineChartGroebnerVerification {
        let groebner_verification = self.certificate.verify();
        LabsAffineChartGroebnerVerification {
            chart_variable: self.chart_variable,
            order: self.certificate.order(),
            generators_match_model: self.generators_match_model(),
            basis_is_groebner: groebner_verification.basis_is_groebner(),
            generators_reduce_to_zero: groebner_verification.generators_reduce_to_zero(),
            basis_size: self.certificate.basis().len(),
            quotient_dimension: self.certificate.quotient_dimension(),
            expected_quotient_length: LABS_SEPTIC_EXPECTED_NODE_COUNT,
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct LabsAffineChartGroebnerVerification {
    chart_variable: usize,
    order: MonomialOrder,
    generators_match_model: bool,
    basis_is_groebner: bool,
    generators_reduce_to_zero: bool,
    basis_size: usize,
    quotient_dimension: Option<usize>,
    expected_quotient_length: usize,
}

impl LabsAffineChartGroebnerVerification {
    pub fn chart_variable(self) -> usize {
        self.chart_variable
    }

    pub fn order(self) -> MonomialOrder {
        self.order
    }

    pub fn generators_match_model(self) -> bool {
        self.generators_match_model
    }

    pub fn basis_is_groebner(self) -> bool {
        self.basis_is_groebner
    }

    pub fn generators_reduce_to_zero(self) -> bool {
        self.generators_reduce_to_zero
    }

    pub fn basis_size(self) -> usize {
        self.basis_size
    }

    pub fn quotient_dimension(self) -> Option<usize> {
        self.quotient_dimension
    }

    pub fn expected_quotient_length(self) -> usize {
        self.expected_quotient_length
    }

    pub fn verified(self) -> bool {
        self.generators_match_model
            && self.basis_is_groebner
            && self.generators_reduce_to_zero
            && self.quotient_dimension == Some(self.expected_quotient_length)
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct LabsAffineChart0HessianBadGroebnerCertificate {
    certificate: GroebnerCertificate<AFFINE_P3_VARIABLE_COUNT, BigCubicAlphaRational>,
}

impl LabsAffineChart0HessianBadGroebnerCertificate {
    pub fn chart_variable(&self) -> usize {
        0
    }

    pub fn certificate(
        &self,
    ) -> &GroebnerCertificate<AFFINE_P3_VARIABLE_COUNT, BigCubicAlphaRational> {
        &self.certificate
    }

    pub fn expected_generators(&self) -> Vec<BigPolynomialA3> {
        labs_affine_chart0_hessian_bad_generators()
            .into_iter()
            .map(cubic_polynomial_to_big_cubic)
            .collect()
    }

    pub fn generators_match_model(&self) -> bool {
        self.certificate.generators() == self.expected_generators().as_slice()
    }

    pub fn verify(&self) -> LabsAffineChart0HessianBadGroebnerVerification {
        let groebner_verification = self.certificate.verify();
        LabsAffineChart0HessianBadGroebnerVerification {
            order: self.certificate.order(),
            generators_match_model: self.generators_match_model(),
            basis_is_groebner: groebner_verification.basis_is_groebner(),
            generators_reduce_to_zero: groebner_verification.generators_reduce_to_zero(),
            basis_size: self.certificate.basis().len(),
            quotient_dimension: self.certificate.quotient_dimension(),
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct LabsAffineChart0HessianBadGroebnerVerification {
    order: MonomialOrder,
    generators_match_model: bool,
    basis_is_groebner: bool,
    generators_reduce_to_zero: bool,
    basis_size: usize,
    quotient_dimension: Option<usize>,
}

impl LabsAffineChart0HessianBadGroebnerVerification {
    pub fn order(self) -> MonomialOrder {
        self.order
    }

    pub fn generators_match_model(self) -> bool {
        self.generators_match_model
    }

    pub fn basis_is_groebner(self) -> bool {
        self.basis_is_groebner
    }

    pub fn generators_reduce_to_zero(self) -> bool {
        self.generators_reduce_to_zero
    }

    pub fn basis_size(self) -> usize {
        self.basis_size
    }

    pub fn quotient_dimension(self) -> Option<usize> {
        self.quotient_dimension
    }

    pub fn verified_empty(self) -> bool {
        self.generators_match_model
            && self.basis_is_groebner
            && self.generators_reduce_to_zero
            && self.quotient_dimension == Some(0)
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct LabsAffineChart0Support15SaturationGroebnerCertificate {
    certificate: GroebnerCertificate<AFFINE_P3_VARIABLE_COUNT, BigCubicAlphaRational>,
}

impl LabsAffineChart0Support15SaturationGroebnerCertificate {
    pub fn chart_variable(&self) -> usize {
        0
    }

    pub fn certificate(
        &self,
    ) -> &GroebnerCertificate<AFFINE_P3_VARIABLE_COUNT, BigCubicAlphaRational> {
        &self.certificate
    }

    pub fn saturation_multiplier(&self) -> BigPolynomialA3 {
        BigPolynomialA3::variable(0)
            .mul(&BigPolynomialA3::variable(1))
            .mul(&BigPolynomialA3::variable(2))
    }

    pub fn expected_quotient_length(&self) -> usize {
        LABS_AFFINE_CHART0_SUPPORT15_SATURATION_LENGTH
    }

    pub fn affine_generators_reduce_to_zero(&self) -> bool {
        let affine_generators = labs_affine_chart_generators(0)
            .into_iter()
            .map(cubic_polynomial_to_big_cubic)
            .collect::<Vec<_>>();

        BigPolynomialA3::all_reduce_to_zero(
            &affine_generators,
            self.certificate.basis(),
            self.certificate.order(),
        )
    }

    pub fn verify(&self) -> LabsAffineChart0Support15SaturationGroebnerVerification {
        let groebner_verification = self.certificate.verify();
        LabsAffineChart0Support15SaturationGroebnerVerification {
            order: self.certificate.order(),
            basis_is_groebner: groebner_verification.basis_is_groebner(),
            saturation_generators_reduce_to_zero: groebner_verification.generators_reduce_to_zero(),
            affine_generators_reduce_to_zero: self.affine_generators_reduce_to_zero(),
            basis_size: self.certificate.basis().len(),
            quotient_dimension: self.certificate.quotient_dimension(),
            expected_quotient_length: self.expected_quotient_length(),
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct LabsAffineChart0Support15SaturationGroebnerVerification {
    order: MonomialOrder,
    basis_is_groebner: bool,
    saturation_generators_reduce_to_zero: bool,
    affine_generators_reduce_to_zero: bool,
    basis_size: usize,
    quotient_dimension: Option<usize>,
    expected_quotient_length: usize,
}

impl LabsAffineChart0Support15SaturationGroebnerVerification {
    pub fn order(self) -> MonomialOrder {
        self.order
    }

    pub fn basis_is_groebner(self) -> bool {
        self.basis_is_groebner
    }

    pub fn saturation_generators_reduce_to_zero(self) -> bool {
        self.saturation_generators_reduce_to_zero
    }

    pub fn affine_generators_reduce_to_zero(self) -> bool {
        self.affine_generators_reduce_to_zero
    }

    pub fn basis_size(self) -> usize {
        self.basis_size
    }

    pub fn quotient_dimension(self) -> Option<usize> {
        self.quotient_dimension
    }

    pub fn expected_quotient_length(self) -> usize {
        self.expected_quotient_length
    }

    pub fn verified_imported_saturation(self) -> bool {
        self.basis_is_groebner
            && self.saturation_generators_reduce_to_zero
            && self.affine_generators_reduce_to_zero
            && self.quotient_dimension == Some(self.expected_quotient_length)
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct LabsProjectiveSupportGroebnerCertificate {
    support: LabsProjectiveSupport,
    certificate: GroebnerCertificate<LABS_PROJECTIVE_STRATUM_VARIABLE_COUNT, BigCubicAlphaRational>,
}

impl LabsProjectiveSupportGroebnerCertificate {
    pub fn support(&self) -> LabsProjectiveSupport {
        self.support
    }

    pub fn certificate(
        &self,
    ) -> &GroebnerCertificate<LABS_PROJECTIVE_STRATUM_VARIABLE_COUNT, BigCubicAlphaRational> {
        &self.certificate
    }

    pub fn expected_generators(&self) -> Vec<BigPolynomialA4> {
        labs_projective_support_stratum_generators(self.support.mask())
            .generators
            .into_iter()
            .map(cubic_polynomial_to_big_cubic)
            .collect()
    }

    pub fn expected_quotient_length(&self) -> usize {
        LABS_PROJECTIVE_SUPPORT_STRATUM_LENGTHS[usize::from(self.support.mask() - 1)]
    }

    pub fn generators_match_model(&self) -> bool {
        self.certificate.generators() == self.expected_generators().as_slice()
    }

    pub fn verify(&self) -> LabsProjectiveSupportGroebnerVerification {
        let groebner_verification = self.certificate.verify();
        LabsProjectiveSupportGroebnerVerification {
            support_mask: self.support.mask(),
            order: self.certificate.order(),
            generators_match_model: self.generators_match_model(),
            basis_is_groebner: groebner_verification.basis_is_groebner(),
            generators_reduce_to_zero: groebner_verification.generators_reduce_to_zero(),
            basis_size: self.certificate.basis().len(),
            quotient_dimension: self.certificate.quotient_dimension(),
            expected_quotient_length: self.expected_quotient_length(),
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct LabsProjectiveSupportGroebnerVerification {
    support_mask: u8,
    order: MonomialOrder,
    generators_match_model: bool,
    basis_is_groebner: bool,
    generators_reduce_to_zero: bool,
    basis_size: usize,
    quotient_dimension: Option<usize>,
    expected_quotient_length: usize,
}

impl LabsProjectiveSupportGroebnerVerification {
    pub fn support_mask(self) -> u8 {
        self.support_mask
    }

    pub fn order(self) -> MonomialOrder {
        self.order
    }

    pub fn generators_match_model(self) -> bool {
        self.generators_match_model
    }

    pub fn basis_is_groebner(self) -> bool {
        self.basis_is_groebner
    }

    pub fn generators_reduce_to_zero(self) -> bool {
        self.generators_reduce_to_zero
    }

    pub fn basis_size(self) -> usize {
        self.basis_size
    }

    pub fn quotient_dimension(self) -> Option<usize> {
        self.quotient_dimension
    }

    pub fn expected_quotient_length(self) -> usize {
        self.expected_quotient_length
    }

    pub fn verified(self) -> bool {
        self.generators_match_model
            && self.basis_is_groebner
            && self.generators_reduce_to_zero
            && self.quotient_dimension == Some(self.expected_quotient_length)
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct LabsSingularSchemeCertificate {
    affine_chart0: LabsAffineChartGroebnerCertificate,
    hessian_bad: LabsAffineChart0HessianBadGroebnerCertificate,
    support15_saturation: LabsAffineChart0Support15SaturationGroebnerCertificate,
    infinity_support_strata: Vec<LabsProjectiveSupportGroebnerCertificate>,
}

impl LabsSingularSchemeCertificate {
    pub fn affine_chart0(&self) -> &LabsAffineChartGroebnerCertificate {
        &self.affine_chart0
    }

    pub fn hessian_bad(&self) -> &LabsAffineChart0HessianBadGroebnerCertificate {
        &self.hessian_bad
    }

    pub fn support15_saturation(&self) -> &LabsAffineChart0Support15SaturationGroebnerCertificate {
        &self.support15_saturation
    }

    pub fn infinity_support_strata(&self) -> &[LabsProjectiveSupportGroebnerCertificate] {
        &self.infinity_support_strata
    }

    pub fn verified_no_infinity(&self) -> bool {
        self.infinity_support_strata.iter().all(|stratum| {
            let Ok(lift) =
                labs_projective_support_grevlex_lift_certificate(stratum.support().mask())
            else {
                return false;
            };
            let verification = stratum.verify();
            verification.verified()
                && verification.quotient_dimension() == Some(0)
                && lift.verifies_targets(
                    stratum.certificate.generators(),
                    stratum.certificate.basis(),
                )
        })
    }

    pub fn verified_projective_length(&self) -> Option<usize> {
        let affine_verification = self.affine_chart0.verify();
        if !affine_verification.verified() || !self.verified_no_infinity() {
            return None;
        }

        affine_verification.quotient_dimension()
    }

    pub fn verified_open_support_length_evidence(&self) -> Option<usize> {
        let saturation_verification = self.support15_saturation.verify();
        saturation_verification
            .verified_imported_saturation()
            .then_some(saturation_verification.quotient_dimension()?)
    }

    pub fn verified_reduced_ordinary_node_count(&self) -> Option<usize> {
        let projective_length = self.verified_projective_length()?;
        if self.hessian_bad.verify().verified_empty() {
            Some(projective_length)
        } else {
            None
        }
    }
}

fn labs_septic_sparse_polynomial() -> PolynomialP3 {
    labs_p_polynomial().sub(&labs_u_polynomial())
}

fn lift_affine3_polynomial_to_stratum(polynomial: PolynomialA3) -> PolynomialA4 {
    PolynomialA4::from_terms(
        polynomial
            .terms()
            .into_iter()
            .map(|term| {
                let affine_exponents = term.exponents();
                let mut stratum_exponents = [0; LABS_PROJECTIVE_STRATUM_VARIABLE_COUNT];
                stratum_exponents[..AFFINE_P3_VARIABLE_COUNT].copy_from_slice(&affine_exponents);
                (term.coefficient(), stratum_exponents)
            })
            .collect(),
    )
}

fn cubic_polynomial_to_big_cubic<const N: usize>(
    polynomial: SparsePolynomial<CubicAlphaRational, N>,
) -> SparsePolynomial<BigCubicAlphaRational, N> {
    polynomial.map_coefficients(|coefficient| BigCubicAlphaRational::from(*coefficient))
}

fn labs_p_polynomial() -> PolynomialP3 {
    let [_w, x, y, z] = variables();
    let radius_squared = x.pow_usize(2).add(&y.pow_usize(2));

    x.mul(
        &x.pow_usize(6)
            .sub(&x.pow_usize(4).mul(&y.pow_usize(2)).scale(q(21)))
            .add(&x.pow_usize(2).mul(&y.pow_usize(4)).scale(q(35)))
            .sub(&y.pow_usize(6).scale(q(7))),
    )
    .add(
        &z.mul(
            &radius_squared
                .pow_usize(3)
                .sub(&z.pow_usize(2).mul(&radius_squared.pow_usize(2)).scale(q(8)))
                .add(&z.pow_usize(4).mul(&radius_squared).scale(q(16))),
        )
        .scale(q(7)),
    )
    .sub(&z.pow_usize(7).scale(q(64)))
}

fn labs_u_polynomial() -> PolynomialP3 {
    let [w, x, y, z] = variables();
    let params = labs_parameters();
    let radius_squared = x.pow_usize(2).add(&y.pow_usize(2));
    let cubic = z
        .add(&w)
        .mul(&radius_squared)
        .add(&z.pow_usize(3).scale(params.a1))
        .add(&z.pow_usize(2).mul(&w).scale(params.a2))
        .add(&z.mul(&w.pow_usize(2)).scale(params.a3))
        .add(&w.pow_usize(3).scale(params.a4));

    z.add(&w.scale(params.a5)).mul(&cubic.pow_usize(2))
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct LabsParameters {
    a1: CubicAlphaRational,
    a2: CubicAlphaRational,
    a3: CubicAlphaRational,
    a4: CubicAlphaRational,
    a5: CubicAlphaRational,
}

fn labs_parameters() -> LabsParameters {
    let alpha = CubicAlphaRational::alpha();
    let alpha_squared = CubicAlphaRational::alpha_squared();
    LabsParameters {
        a1: -alpha_squared.scale(r(12, 7)) - alpha.scale(r(384, 49)) - q(8).scale(r(1, 7)),
        a2: -alpha_squared.scale(r(32, 7)) + alpha.scale(r(24, 49)) - q(4),
        a3: -alpha_squared.scale(r(4, 1)) + alpha.scale(r(24, 49)) - q(4),
        a4: -alpha_squared.scale(r(8, 7)) + alpha.scale(r(8, 49)) - q(8).scale(r(1, 7)),
        a5: alpha_squared.scale(r(49, 1)) - alpha.scale(r(7, 1)) + q(50),
    }
}

trait CubicScale {
    fn scale(self, scalar: Rational) -> Self;
}

impl CubicScale for CubicAlphaRational {
    fn scale(self, scalar: Rational) -> Self {
        Self::new(
            self.coefficients[0] * scalar,
            self.coefficients[1] * scalar,
            self.coefficients[2] * scalar,
        )
    }
}

fn multiplication_matrix(value: CubicAlphaRational) -> [[Rational; 3]; 3] {
    let basis = [
        CubicAlphaRational::ONE,
        CubicAlphaRational::alpha(),
        CubicAlphaRational::alpha_squared(),
    ];
    std::array::from_fn(|row| {
        std::array::from_fn(|column| (value * basis[column]).coefficients()[row])
    })
}

fn big_multiplication_matrix(value: BigCubicAlphaRational) -> [[BigRational; 3]; 3] {
    let basis = [
        BigCubicAlphaRational::from_i64(1),
        BigCubicAlphaRational::alpha(),
        BigCubicAlphaRational::alpha_squared(),
    ];
    std::array::from_fn(|row| {
        std::array::from_fn(|column| {
            (value.clone() * basis[column].clone()).coefficients()[row].clone()
        })
    })
}

fn parse_big_cubic_alpha_rational(value: &str) -> Result<BigCubicAlphaRational, String> {
    let mut value = value.trim();
    if value.is_empty() {
        return Err("empty cubic alpha rational".to_string());
    }
    while let Some(stripped) = value
        .strip_prefix('(')
        .and_then(|inner| inner.strip_suffix(')'))
    {
        value = stripped.trim();
    }
    if value == "0" {
        return Ok(BigCubicAlphaRational::from_i64(0));
    }

    let normalized = value.replace([' ', '*'], "").replace("a^2", "a2");
    let terms = split_signed_terms(&normalized)?;
    let mut coefficients = std::array::from_fn::<_, 3, _>(|_| BigRational::from_i64(0));
    for term in terms {
        if let Some(coefficient) = term.strip_suffix("a2") {
            coefficients[2] = coefficients[2].clone() + parse_big_alpha_coefficient(coefficient)?;
        } else if let Some(coefficient) = term.strip_suffix('a') {
            coefficients[1] = coefficients[1].clone() + parse_big_alpha_coefficient(coefficient)?;
        } else {
            coefficients[0] = coefficients[0].clone()
                + term
                    .parse::<BigRational>()
                    .map_err(|error| format!("invalid rational term `{term}`: {error}"))?;
        }
    }

    Ok(BigCubicAlphaRational::new(
        coefficients[0].clone(),
        coefficients[1].clone(),
        coefficients[2].clone(),
    ))
}

fn split_signed_terms(value: &str) -> Result<Vec<String>, String> {
    if value.is_empty() {
        return Err("empty cubic alpha rational".to_string());
    }

    let mut terms = Vec::new();
    let mut start = 0;
    for (index, byte) in value.bytes().enumerate().skip(1) {
        if byte == b'+' || byte == b'-' {
            terms.push(value[start..index].to_string());
            start = index;
        }
    }
    terms.push(value[start..].to_string());
    Ok(terms)
}

fn parse_big_alpha_coefficient(value: &str) -> Result<BigRational, String> {
    match value {
        "" | "+" => Ok(BigRational::from_i64(1)),
        "-" => Ok(BigRational::from_i64(-1)),
        _ => value
            .parse::<BigRational>()
            .map_err(|error| format!("invalid alpha coefficient `{value}`: {error}")),
    }
}

fn affine_hessian_determinant(polynomial: &PolynomialA3) -> PolynomialA3 {
    let h = std::array::from_fn::<_, AFFINE_P3_VARIABLE_COUNT, _>(|row| {
        std::array::from_fn::<_, AFFINE_P3_VARIABLE_COUNT, _>(|col| {
            polynomial.partial_derivative(row).partial_derivative(col)
        })
    });

    h[0][0]
        .mul(&h[1][1])
        .mul(&h[2][2])
        .add(&h[0][1].mul(&h[1][2]).mul(&h[2][0]).scale(q(2)))
        .sub(&h[0][0].mul(&h[1][2].pow_usize(2)))
        .sub(&h[1][1].mul(&h[0][2].pow_usize(2)))
        .sub(&h[2][2].mul(&h[0][1].pow_usize(2)))
}

fn variables() -> [PolynomialP3; P3_VARIABLE_COUNT] {
    std::array::from_fn(PolynomialP3::variable)
}

fn q(value: i64) -> CubicAlphaRational {
    CubicAlphaRational::from_i64(value)
}

fn r(numerator: i64, denominator: i64) -> Rational {
    Rational::new(numerator.into(), denominator.into())
}

fn big_r(numerator: i64, denominator: i64) -> BigRational {
    BigRational::from(Rational::new(numerator.into(), denominator.into()))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn cubic_alpha_field_satisfies_labs_minimal_polynomial() {
        assert!(labs_alpha_polynomial_value().is_zero());

        let alpha = CubicAlphaRational::alpha();
        assert_eq!(alpha.pow_usize(3), -alpha - q(1).scale(r(1, 7)));
        assert_eq!(alpha / alpha, CubicAlphaRational::ONE);
    }

    #[test]
    fn labs_septic_has_degree_seven_over_cubic_field() {
        let polynomial = labs_septic_polynomial();
        assert_eq!(polynomial.degree(), 7);
        assert!(polynomial.terms().len() > 20);
        assert!(
            polynomial
                .terms()
                .iter()
                .all(|term| term.exponents().iter().sum::<usize>() == 7)
        );
    }

    #[test]
    fn labs_septic_evaluation_and_gradient_are_exact() {
        let polynomial = labs_septic_polynomial();
        let point = [
            CubicAlphaRational::ZERO,
            CubicAlphaRational::ONE,
            CubicAlphaRational::ZERO,
            CubicAlphaRational::ZERO,
        ];

        assert_eq!(polynomial.evaluate(&point), CubicAlphaRational::ONE);
        assert_eq!(polynomial.gradient_at(&point).len(), P3_VARIABLE_COUNT);
        assert_eq!(
            polynomial.affine_singular_generators(0).len(),
            P3_VARIABLE_COUNT
        );
    }

    #[test]
    fn labs_plane_section_orbit_count_matches_ninety_nine() {
        assert_eq!(labs_septic_expected_orbit_count_from_plane_section(), 99);
    }

    #[test]
    fn big_cubic_alpha_rational_parses_singular_coefficients() {
        assert_eq!(
            "(a^2-a-1/7)"
                .parse::<BigCubicAlphaRational>()
                .expect("coefficient parses"),
            BigCubicAlphaRational::alpha_squared()
                - BigCubicAlphaRational::alpha()
                - BigCubicAlphaRational::from_rational(big_r(1, 7))
        );
        assert_eq!(
            "(a2-a-1/7)"
                .parse::<BigCubicAlphaRational>()
                .expect("coefficient parses"),
            BigCubicAlphaRational::alpha_squared()
                - BigCubicAlphaRational::alpha()
                - BigCubicAlphaRational::from_rational(big_r(1, 7))
        );
        assert_eq!(
            "(932/3105a2-3733/21735a+5296/21735)"
                .parse::<BigCubicAlphaRational>()
                .expect("coefficient parses")
                .coefficients()
                .clone(),
            [big_r(5296, 21735), -big_r(3733, 21735), big_r(932, 3105)]
        );
    }

    #[test]
    fn affine_chart0_groebner_certificate_imports_length_ninety_nine() {
        let certificate =
            labs_affine_chart0_grevlex_certificate().expect("affine chart certificate parses");

        assert_eq!(certificate.chart_variable(), 0);
        assert_eq!(certificate.certificate().order(), MonomialOrder::GrevLex);
        assert_eq!(certificate.certificate().basis().len(), 28);
        assert!(certificate.generators_match_model());
        assert_eq!(certificate.certificate().quotient_dimension(), Some(99));
    }

    #[test]
    fn affine_chart0_hessian_bad_certificate_verifies_empty() {
        let certificate = labs_affine_chart0_hessian_bad_grevlex_certificate()
            .expect("affine Hessian-bad certificate parses");

        assert_eq!(certificate.chart_variable(), 0);
        assert_eq!(certificate.certificate().order(), MonomialOrder::GrevLex);
        assert_eq!(certificate.certificate().basis().len(), 1);
        assert_eq!(certificate.certificate().quotient_dimension(), Some(0));
        assert_eq!(labs_affine_chart0_hessian_bad_generators().len(), 5);
        assert!(certificate.generators_match_model());

        let verification = certificate.verify();
        assert!(verification.generators_match_model());
        assert!(verification.basis_is_groebner());
        assert!(verification.generators_reduce_to_zero());
        assert_eq!(verification.basis_size(), 1);
        assert_eq!(verification.quotient_dimension(), Some(0));
        assert!(verification.verified_empty());
    }

    #[test]
    fn affine_chart0_support15_saturation_certificate_imports_open_length() {
        let certificate = labs_affine_chart0_support15_saturation_grevlex_certificate()
            .expect("support15 saturation certificate parses");

        assert_eq!(certificate.chart_variable(), 0);
        assert_eq!(certificate.certificate().order(), MonomialOrder::GrevLex);
        assert_eq!(certificate.certificate().basis().len(), 15);
        assert_eq!(
            certificate.certificate().quotient_dimension(),
            Some(LABS_AFFINE_CHART0_SUPPORT15_SATURATION_LENGTH)
        );
        assert_eq!(certificate.saturation_multiplier().degree(), 3);
    }

    #[test]
    #[ignore = "support15 saturation Buchberger verification is a heavy certificate check"]
    fn affine_chart0_support15_saturation_certificate_buchberger_verifies_open_length() {
        let certificate = labs_affine_chart0_support15_saturation_grevlex_certificate()
            .expect("support15 saturation certificate parses");
        let verification = certificate.verify();

        assert!(verification.basis_is_groebner());
        assert!(verification.saturation_generators_reduce_to_zero());
        assert!(verification.affine_generators_reduce_to_zero());
        assert_eq!(verification.basis_size(), 15);
        assert_eq!(
            verification.quotient_dimension(),
            Some(LABS_AFFINE_CHART0_SUPPORT15_SATURATION_LENGTH)
        );
        assert!(verification.verified_imported_saturation());
    }

    #[test]
    fn completed_projective_support_certificates_import_boundary_lengths() {
        assert_eq!(
            LABS_PROJECTIVE_SUPPORT_STRATUM_LENGTHS
                .into_iter()
                .sum::<usize>(),
            LABS_SEPTIC_EXPECTED_NODE_COUNT
        );
        assert_eq!(LABS_PROJECTIVE_SUPPORT_STRATUM_LENGTHS[8], 1);
        assert_eq!(LABS_PROJECTIVE_SUPPORT_STRATUM_LENGTHS[10], 14);
        assert_eq!(LABS_PROJECTIVE_SUPPORT_STRATUM_LENGTHS[14], 84);

        for support_mask in 1..=14 {
            let certificate = labs_projective_support_grevlex_certificate(support_mask)
                .expect("completed support certificate parses");
            assert!(certificate.generators_match_model(), "{support_mask}");
            assert_eq!(
                certificate.certificate().quotient_dimension(),
                Some(certificate.expected_quotient_length()),
                "{support_mask}"
            );
        }
    }

    #[test]
    fn infinity_support_certificates_import_empty_lengths() {
        let strata =
            labs_infinity_support_grevlex_certificates().expect("infinity certificates parse");

        assert_eq!(strata.len(), LABS_INFINITY_SUPPORT_MASKS.len());

        for stratum in &strata {
            assert_eq!(stratum.expected_quotient_length(), 0);
            assert_eq!(stratum.certificate().quotient_dimension(), Some(0));
        }
    }

    #[test]
    fn singular_scheme_certificate_imports_economic_cover() {
        let certificate =
            labs_singular_scheme_certificate().expect("singular scheme certificate parses");

        assert_eq!(
            certificate
                .affine_chart0()
                .certificate()
                .quotient_dimension(),
            Some(LABS_SEPTIC_EXPECTED_NODE_COUNT)
        );
        assert_eq!(
            certificate
                .support15_saturation()
                .certificate()
                .quotient_dimension(),
            Some(LABS_AFFINE_CHART0_SUPPORT15_SATURATION_LENGTH)
        );
        assert_eq!(
            certificate.infinity_support_strata().len(),
            LABS_INFINITY_SUPPORT_MASKS.len()
        );
    }

    #[test]
    #[ignore = "projective closure replays heavy affine, infinity, and support15 certificates"]
    fn singular_scheme_certificate_verifies_projective_length_and_ordinary_nodes() {
        let certificate =
            labs_singular_scheme_certificate().expect("singular scheme certificate parses");

        assert_eq!(
            certificate.verified_projective_length(),
            Some(LABS_SEPTIC_EXPECTED_NODE_COUNT)
        );
        assert_eq!(
            certificate.verified_open_support_length_evidence(),
            Some(LABS_AFFINE_CHART0_SUPPORT15_SATURATION_LENGTH)
        );
        assert_eq!(
            certificate.verified_reduced_ordinary_node_count(),
            Some(LABS_SEPTIC_EXPECTED_NODE_COUNT)
        );
    }

    #[test]
    #[ignore = "full Buchberger verification is intentionally run as a heavy certificate check"]
    fn affine_chart0_groebner_certificate_buchberger_verifies_length_ninety_nine() {
        let certificate =
            labs_affine_chart0_grevlex_certificate().expect("affine chart certificate parses");
        let verification = certificate.verify();

        assert!(verification.generators_match_model());
        assert!(verification.basis_is_groebner());
        assert!(verification.generators_reduce_to_zero());
        assert_eq!(verification.basis_size(), 28);
        assert_eq!(verification.quotient_dimension(), Some(99));
        assert!(verification.verified());
    }

    #[test]
    #[ignore = "full Buchberger verification is intentionally run as a heavy certificate check"]
    fn completed_projective_support_certificates_buchberger_verify_boundary_lengths() {
        for support_mask in 1..=14 {
            let certificate = labs_projective_support_grevlex_certificate(support_mask)
                .expect("completed support certificate parses");
            let verification = certificate.verify();
            assert!(
                verification.verified(),
                "support {} failed: {:?}",
                support_mask,
                verification
            );
        }
    }

    #[test]
    fn projective_support_strata_are_well_formed() {
        for support_mask in 1..=LABS_PROJECTIVE_SUPPORT_STRATUM_COUNT {
            let stratum = labs_projective_support_stratum_generators(support_mask as u8);
            assert_eq!(
                stratum.generators().len(),
                AFFINE_P3_VARIABLE_COUNT + 2 + AFFINE_P3_VARIABLE_COUNT
                    - (stratum.support().projective_variables().len() - 1)
            );
            assert!(
                stratum
                    .generators()
                    .iter()
                    .all(|generator| generator.degree() <= 7)
            );
        }
    }
}
