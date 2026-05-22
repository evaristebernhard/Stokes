use nodal_core::{
    AFFINE_P3_VARIABLE_COUNT, BigQuadraticRational, BigRational, GroebnerCertificate,
    GroebnerCertificateParseError, GroebnerLiftCertificate, HomogeneousPolynomialP3, Matrix,
    MonomialOrder, P3_VARIABLE_COUNT, ProjectivePoint, ProjectiveSupport, QuadraticRational,
    Rational, SparsePolynomial, p3_affine_variable_indices, parse_groebner_lift_certificate,
};
use std::fmt;

type PolynomialP3 = SparsePolynomial<Rational, P3_VARIABLE_COUNT>;
type PolynomialA3 = SparsePolynomial<Rational, AFFINE_P3_VARIABLE_COUNT>;
type PolynomialA4 = SparsePolynomial<Rational, TOGLIATTI_PROJECTIVE_STRATUM_VARIABLE_COUNT>;
type BigPolynomialA3 = SparsePolynomial<BigRational, AFFINE_P3_VARIABLE_COUNT>;
type BigPolynomialA4 = SparsePolynomial<BigRational, TOGLIATTI_PROJECTIVE_STRATUM_VARIABLE_COUNT>;
type QuadraticPolynomialP3 = SparsePolynomial<QuadraticRational, P3_VARIABLE_COUNT>;
type QuadraticPolynomialA3 = SparsePolynomial<QuadraticRational, AFFINE_P3_VARIABLE_COUNT>;
type QuadraticPolynomialA4 =
    SparsePolynomial<QuadraticRational, TOGLIATTI_PROJECTIVE_STRATUM_VARIABLE_COUNT>;
pub type TogliattiProjectiveSupport = ProjectiveSupport<P3_VARIABLE_COUNT>;
pub type QuadraticGroebnerLiftCertificate<const N: usize> =
    GroebnerLiftCertificate<N, BigQuadraticRational>;

const TOGLIATTI_AFFINE_CHART_GREVLEX_CERTIFICATES: [&str; P3_VARIABLE_COUNT] = [
    include_str!("../certificates/togliatti-chart0-grevlex.cert"),
    include_str!("../certificates/togliatti-chart1-grevlex.cert"),
    include_str!("../certificates/togliatti-chart2-grevlex.cert"),
    include_str!("../certificates/togliatti-chart3-grevlex.cert"),
];

const TOGLIATTI_PROJECTIVE_SUPPORT_GREVLEX_CERTIFICATES: [&str;
    TOGLIATTI_PROJECTIVE_SUPPORT_STRATUM_COUNT] = [
    include_str!("../certificates/togliatti-support-01-grevlex.cert"),
    include_str!("../certificates/togliatti-support-02-grevlex.cert"),
    include_str!("../certificates/togliatti-support-03-grevlex.cert"),
    include_str!("../certificates/togliatti-support-04-grevlex.cert"),
    include_str!("../certificates/togliatti-support-05-grevlex.cert"),
    include_str!("../certificates/togliatti-support-06-grevlex.cert"),
    include_str!("../certificates/togliatti-support-07-grevlex.cert"),
    include_str!("../certificates/togliatti-support-08-grevlex.cert"),
    include_str!("../certificates/togliatti-support-09-grevlex.cert"),
    include_str!("../certificates/togliatti-support-10-grevlex.cert"),
    include_str!("../certificates/togliatti-support-11-grevlex.cert"),
    include_str!("../certificates/togliatti-support-12-grevlex.cert"),
    include_str!("../certificates/togliatti-support-13-grevlex.cert"),
    include_str!("../certificates/togliatti-support-14-grevlex.cert"),
    include_str!("../certificates/togliatti-support-15-grevlex.cert"),
];

const SPECIAL_TOGLIATTI_AFFINE_CHART3_GREVLEX_CERTIFICATE: &str =
    include_str!("../certificates/special-togliatti-chart3-grevlex.cert");
const SPECIAL_TOGLIATTI_AFFINE_CHART3_GREVLEX_LIFT_CERTIFICATE: &str =
    include_str!("../certificates/special-togliatti-chart3-grevlex.lift");
const SPECIAL_TOGLIATTI_AFFINE_CHART3_HESSIAN_BAD_GREVLEX_CERTIFICATE: &str =
    include_str!("../certificates/special-togliatti-chart3-hessian-bad-grevlex.cert");
const SPECIAL_TOGLIATTI_AFFINE_CHART3_HESSIAN_BAD_GREVLEX_LIFT_CERTIFICATE: &str =
    include_str!("../certificates/special-togliatti-chart3-hessian-bad-grevlex.lift");
const SPECIAL_TOGLIATTI_INFINITY_SUPPORT_GREVLEX_CERTIFICATES: [&str; 7] = [
    include_str!("../certificates/special-togliatti-infinity-support-01-grevlex.cert"),
    include_str!("../certificates/special-togliatti-infinity-support-02-grevlex.cert"),
    include_str!("../certificates/special-togliatti-infinity-support-03-grevlex.cert"),
    include_str!("../certificates/special-togliatti-infinity-support-04-grevlex.cert"),
    include_str!("../certificates/special-togliatti-infinity-support-05-grevlex.cert"),
    include_str!("../certificates/special-togliatti-infinity-support-06-grevlex.cert"),
    include_str!("../certificates/special-togliatti-infinity-support-07-grevlex.cert"),
];
const SPECIAL_TOGLIATTI_INFINITY_SUPPORT_GREVLEX_LIFT_CERTIFICATES: [&str; 7] = [
    include_str!("../certificates/special-togliatti-infinity-support-01-grevlex.lift"),
    include_str!("../certificates/special-togliatti-infinity-support-02-grevlex.lift"),
    include_str!("../certificates/special-togliatti-infinity-support-03-grevlex.lift"),
    include_str!("../certificates/special-togliatti-infinity-support-04-grevlex.lift"),
    include_str!("../certificates/special-togliatti-infinity-support-05-grevlex.lift"),
    include_str!("../certificates/special-togliatti-infinity-support-06-grevlex.lift"),
    include_str!("../certificates/special-togliatti-infinity-support-07-grevlex.lift"),
];

pub const TOGLIATTI_AFFINE_CHART_QUOTIENT_LENGTH: usize = 16;
pub const SPECIAL_TOGLIATTI_AFFINE_CHART3_QUOTIENT_LENGTH: usize = 31;
pub const SPECIAL_TOGLIATTI_HESSIAN_BAD_QUOTIENT_LENGTH: usize = 0;
pub const SPECIAL_TOGLIATTI_INFINITY_SUPPORT_STRATUM_COUNT: usize = 7;
pub const TOGLIATTI_PROJECTIVE_STRATUM_VARIABLE_COUNT: usize = AFFINE_P3_VARIABLE_COUNT + 1;
pub const TOGLIATTI_PROJECTIVE_SUPPORT_STRATUM_COUNT: usize = (1 << P3_VARIABLE_COUNT) - 1;
pub const TOGLIATTI_PROJECTIVE_SUPPORT_STRATUM_LENGTHS: [usize;
    TOGLIATTI_PROJECTIVE_SUPPORT_STRATUM_COUNT] = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16];

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct QuinticSurface {
    polynomial: HomogeneousPolynomialP3,
}

impl QuinticSurface {
    pub fn new(polynomial: HomogeneousPolynomialP3) -> Self {
        assert_eq!(polynomial.degree(), 5, "expected a quintic surface");
        Self { polynomial }
    }

    pub fn polynomial(&self) -> &HomogeneousPolynomialP3 {
        &self.polynomial
    }

    pub fn verify_node(&self, point: ProjectivePoint) -> NodeVerification {
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
                && gradient.into_iter().all(Rational::is_zero)
                && hessian_rank == 3,
            hessian,
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct NodeVerification {
    point: ProjectivePoint,
    value: Rational,
    gradient: [Rational; 4],
    hessian_rank: usize,
    ordinary_double_point: bool,
    hessian: Matrix,
}

impl NodeVerification {
    pub fn point(&self) -> &ProjectivePoint {
        &self.point
    }

    pub fn value(&self) -> Rational {
        self.value
    }

    pub fn gradient(&self) -> [Rational; 4] {
        self.gradient
    }

    pub fn hessian_rank(&self) -> usize {
        self.hessian_rank
    }

    pub fn ordinary_double_point(&self) -> bool {
        self.ordinary_double_point
    }

    pub fn hessian(&self) -> &Matrix {
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

pub fn togliatti_quintic() -> QuinticSurface {
    QuinticSurface::new(HomogeneousPolynomialP3::from(
        togliatti_determinant_polynomial(),
    ))
}

pub fn special_togliatti_quintic_polynomial() -> HomogeneousPolynomialP3<QuadraticRational> {
    HomogeneousPolynomialP3::from(special_togliatti_polynomial())
}

pub fn special_togliatti_affine_chart_generators(
    chart_variable: usize,
) -> Vec<QuadraticPolynomialA3> {
    special_togliatti_quintic_polynomial().affine_singular_generators(chart_variable)
}

pub fn special_togliatti_affine_chart3_hessian_degenerate_generators() -> Vec<QuadraticPolynomialA3>
{
    let affine_polynomial = special_togliatti_quintic_polynomial().dehomogenize(3);
    let mut generators = special_togliatti_affine_chart_generators(3);
    generators.push(affine_hessian_determinant(&affine_polynomial));
    generators
}

pub fn special_togliatti_infinity_support_stratum_generators(
    support_mask: u8,
) -> TogliattiSpecialInfinitySupportStratumGenerators {
    assert!(
        (1..=7).contains(&support_mask),
        "infinity support mask must be in 1..=7"
    );

    let support = TogliattiProjectiveSupport::new(support_mask);
    let chart_generators = special_togliatti_affine_chart_generators(support.chart_variable());
    let affine_projective_indices =
        togliatti_affine_chart_variable_indices(support.chart_variable());
    let mut generators = chart_generators
        .into_iter()
        .map(lift_quadratic_affine3_polynomial_to_stratum)
        .collect::<Vec<_>>();

    for (affine_variable, &projective_variable) in affine_projective_indices.iter().enumerate() {
        if !support.contains_projective_variable(projective_variable) {
            generators.push(QuadraticPolynomialA4::variable(affine_variable));
        }
    }

    let mut nonzero_product_exponents = [0; TOGLIATTI_PROJECTIVE_STRATUM_VARIABLE_COUNT];
    for (affine_variable, &projective_variable) in affine_projective_indices.iter().enumerate() {
        if support.contains_projective_variable(projective_variable) {
            nonzero_product_exponents[affine_variable] = 1;
        }
    }
    nonzero_product_exponents[AFFINE_P3_VARIABLE_COUNT] = 1;
    generators.push(QuadraticPolynomialA4::from_terms(vec![
        (QuadraticRational::ONE, nonzero_product_exponents),
        (
            -QuadraticRational::ONE,
            [0; TOGLIATTI_PROJECTIVE_STRATUM_VARIABLE_COUNT],
        ),
    ]));

    TogliattiSpecialInfinitySupportStratumGenerators {
        support,
        affine_projective_indices,
        generators,
    }
}

/// Catanese et al., Proposition 130, prove that this explicit quintic has
/// 31 nodes and no other singularities.
pub fn togliatti_literature_node_count() -> usize {
    31
}

/// Beauville's theorem gives the sharp upper bound for quintic nodal surfaces.
pub fn beauville_maximum_node_count() -> usize {
    31
}

pub fn togliatti_matrix_entry_degrees() -> [[usize; 3]; 3] {
    [[1, 1, 2], [1, 1, 2], [2, 2, 3]]
}

pub fn togliatti_affine_chart_variable_indices(
    chart_variable: usize,
) -> [usize; AFFINE_P3_VARIABLE_COUNT] {
    p3_affine_variable_indices(chart_variable)
}

pub fn togliatti_affine_chart_generators(chart_variable: usize) -> Vec<PolynomialA3> {
    togliatti_quintic()
        .polynomial()
        .affine_singular_generators(chart_variable)
}

pub fn togliatti_projective_support_stratum_generators(
    support_mask: u8,
) -> TogliattiProjectiveSupportStratumGenerators {
    let support = TogliattiProjectiveSupport::new(support_mask);
    let chart_generators = togliatti_affine_chart_generators(support.chart_variable());
    let affine_projective_indices =
        togliatti_affine_chart_variable_indices(support.chart_variable());
    let mut generators = chart_generators
        .into_iter()
        .map(lift_affine3_polynomial_to_stratum)
        .collect::<Vec<_>>();

    for (affine_variable, &projective_variable) in affine_projective_indices.iter().enumerate() {
        if !support.contains_projective_variable(projective_variable) {
            generators.push(PolynomialA4::variable(affine_variable));
        }
    }

    let mut nonzero_product_exponents = [0; TOGLIATTI_PROJECTIVE_STRATUM_VARIABLE_COUNT];
    for (affine_variable, &projective_variable) in affine_projective_indices.iter().enumerate() {
        if support.contains_projective_variable(projective_variable) {
            nonzero_product_exponents[affine_variable] = 1;
        }
    }
    nonzero_product_exponents[AFFINE_P3_VARIABLE_COUNT] = 1;
    generators.push(PolynomialA4::from_terms(vec![
        (Rational::ONE, nonzero_product_exponents),
        (
            -Rational::ONE,
            [0; TOGLIATTI_PROJECTIVE_STRATUM_VARIABLE_COUNT],
        ),
    ]));

    TogliattiProjectiveSupportStratumGenerators {
        support,
        affine_projective_indices,
        generators,
    }
}

pub fn togliatti_affine_chart_grevlex_certificate(
    chart_variable: usize,
) -> Result<TogliattiAffineChartGroebnerCertificate, GroebnerCertificateParseError> {
    assert!(
        chart_variable < P3_VARIABLE_COUNT,
        "P3 chart variable index out of range"
    );

    let certificate = TOGLIATTI_AFFINE_CHART_GREVLEX_CERTIFICATES[chart_variable]
        .parse::<GroebnerCertificate<AFFINE_P3_VARIABLE_COUNT, BigRational>>()?;

    Ok(TogliattiAffineChartGroebnerCertificate {
        chart_variable,
        projective_variable_indices: togliatti_affine_chart_variable_indices(chart_variable),
        certificate,
    })
}

pub fn togliatti_affine_chart_grevlex_certificates()
-> Result<Vec<TogliattiAffineChartGroebnerCertificate>, GroebnerCertificateParseError> {
    (0..P3_VARIABLE_COUNT)
        .map(togliatti_affine_chart_grevlex_certificate)
        .collect()
}

pub fn togliatti_projective_support_grevlex_certificate(
    support_mask: u8,
) -> Result<TogliattiProjectiveSupportGroebnerCertificate, GroebnerCertificateParseError> {
    let support = TogliattiProjectiveSupport::new(support_mask);
    let certificate = TOGLIATTI_PROJECTIVE_SUPPORT_GREVLEX_CERTIFICATES
        [usize::from(support_mask - 1)]
    .parse::<GroebnerCertificate<TOGLIATTI_PROJECTIVE_STRATUM_VARIABLE_COUNT, BigRational>>()?;

    Ok(TogliattiProjectiveSupportGroebnerCertificate {
        support,
        certificate,
    })
}

pub fn togliatti_projective_support_grevlex_certificates()
-> Result<Vec<TogliattiProjectiveSupportGroebnerCertificate>, GroebnerCertificateParseError> {
    (1..=TOGLIATTI_PROJECTIVE_SUPPORT_STRATUM_COUNT)
        .map(|support_mask| togliatti_projective_support_grevlex_certificate(support_mask as u8))
        .collect()
}

pub fn togliatti_singular_scheme_certificate()
-> Result<TogliattiSingularSchemeCertificate, GroebnerCertificateParseError> {
    Ok(TogliattiSingularSchemeCertificate {
        support_strata: togliatti_projective_support_grevlex_certificates()?,
    })
}

pub fn special_togliatti_affine_chart3_grevlex_certificate()
-> Result<SpecialTogliattiAffineChartGroebnerCertificate, GroebnerCertificateParseError> {
    let certificate = SPECIAL_TOGLIATTI_AFFINE_CHART3_GREVLEX_CERTIFICATE
        .parse::<GroebnerCertificate<AFFINE_P3_VARIABLE_COUNT, QuadraticRational>>()?;

    Ok(SpecialTogliattiAffineChartGroebnerCertificate { certificate })
}

pub fn special_togliatti_affine_chart3_grevlex_lift_certificate()
-> Result<QuadraticGroebnerLiftCertificate<AFFINE_P3_VARIABLE_COUNT>, String> {
    parse_groebner_lift_certificate(SPECIAL_TOGLIATTI_AFFINE_CHART3_GREVLEX_LIFT_CERTIFICATE)
}

pub fn special_togliatti_hessian_degenerate_grevlex_certificate()
-> Result<SpecialTogliattiHessianDegenerateGroebnerCertificate, GroebnerCertificateParseError> {
    let certificate = SPECIAL_TOGLIATTI_AFFINE_CHART3_HESSIAN_BAD_GREVLEX_CERTIFICATE
        .parse::<GroebnerCertificate<AFFINE_P3_VARIABLE_COUNT, QuadraticRational>>(
    )?;

    Ok(SpecialTogliattiHessianDegenerateGroebnerCertificate { certificate })
}

pub fn special_togliatti_hessian_degenerate_grevlex_lift_certificate()
-> Result<QuadraticGroebnerLiftCertificate<AFFINE_P3_VARIABLE_COUNT>, String> {
    parse_groebner_lift_certificate(
        SPECIAL_TOGLIATTI_AFFINE_CHART3_HESSIAN_BAD_GREVLEX_LIFT_CERTIFICATE,
    )
}

pub fn special_togliatti_infinity_support_grevlex_certificate(
    support_mask: u8,
) -> Result<SpecialTogliattiInfinitySupportGroebnerCertificate, GroebnerCertificateParseError> {
    assert!(
        (1..=7).contains(&support_mask),
        "infinity support mask must be in 1..=7"
    );
    let certificate = SPECIAL_TOGLIATTI_INFINITY_SUPPORT_GREVLEX_CERTIFICATES
        [usize::from(support_mask - 1)]
    .parse::<GroebnerCertificate<TOGLIATTI_PROJECTIVE_STRATUM_VARIABLE_COUNT, QuadraticRational>>(
    )?;

    Ok(SpecialTogliattiInfinitySupportGroebnerCertificate {
        support: TogliattiProjectiveSupport::new(support_mask),
        certificate,
    })
}

pub fn special_togliatti_infinity_support_grevlex_lift_certificate(
    support_mask: u8,
) -> Result<QuadraticGroebnerLiftCertificate<TOGLIATTI_PROJECTIVE_STRATUM_VARIABLE_COUNT>, String> {
    let index = usize::from(support_mask)
        .checked_sub(1)
        .filter(|&index| index < SPECIAL_TOGLIATTI_INFINITY_SUPPORT_STRATUM_COUNT)
        .ok_or_else(|| format!("support mask {support_mask} is out of range"))?;

    parse_groebner_lift_certificate(
        SPECIAL_TOGLIATTI_INFINITY_SUPPORT_GREVLEX_LIFT_CERTIFICATES[index],
    )
}

pub fn special_togliatti_infinity_support_grevlex_certificates()
-> Result<Vec<SpecialTogliattiInfinitySupportGroebnerCertificate>, GroebnerCertificateParseError> {
    (1..=SPECIAL_TOGLIATTI_INFINITY_SUPPORT_STRATUM_COUNT)
        .map(|support_mask| {
            special_togliatti_infinity_support_grevlex_certificate(support_mask as u8)
        })
        .collect()
}

pub fn special_togliatti_infinity_support_grevlex_lift_certificates() -> Result<
    Vec<QuadraticGroebnerLiftCertificate<TOGLIATTI_PROJECTIVE_STRATUM_VARIABLE_COUNT>>,
    String,
> {
    (1..=SPECIAL_TOGLIATTI_INFINITY_SUPPORT_STRATUM_COUNT)
        .map(|support_mask| {
            special_togliatti_infinity_support_grevlex_lift_certificate(support_mask as u8)
        })
        .collect()
}

pub fn special_togliatti_singular_scheme_certificate()
-> Result<SpecialTogliattiSingularSchemeCertificate, String> {
    Ok(SpecialTogliattiSingularSchemeCertificate {
        affine_chart3: special_togliatti_affine_chart3_grevlex_certificate()
            .map_err(|error| error.to_string())?,
        affine_chart3_lift: special_togliatti_affine_chart3_grevlex_lift_certificate()?,
        hessian_degenerate: special_togliatti_hessian_degenerate_grevlex_certificate()
            .map_err(|error| error.to_string())?,
        hessian_degenerate_lift: special_togliatti_hessian_degenerate_grevlex_lift_certificate()?,
        infinity_support_strata: special_togliatti_infinity_support_grevlex_certificates()
            .map_err(|error| error.to_string())?,
        infinity_support_lifts: special_togliatti_infinity_support_grevlex_lift_certificates()?,
    })
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TogliattiProjectiveSupportStratumGenerators {
    support: TogliattiProjectiveSupport,
    affine_projective_indices: [usize; AFFINE_P3_VARIABLE_COUNT],
    generators: Vec<PolynomialA4>,
}

impl TogliattiProjectiveSupportStratumGenerators {
    pub fn support(&self) -> TogliattiProjectiveSupport {
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
pub struct TogliattiSpecialInfinitySupportStratumGenerators {
    support: TogliattiProjectiveSupport,
    affine_projective_indices: [usize; AFFINE_P3_VARIABLE_COUNT],
    generators: Vec<QuadraticPolynomialA4>,
}

impl TogliattiSpecialInfinitySupportStratumGenerators {
    pub fn support(&self) -> TogliattiProjectiveSupport {
        self.support
    }

    pub fn chart_variable(&self) -> usize {
        self.support.chart_variable()
    }

    pub fn affine_projective_indices(&self) -> [usize; AFFINE_P3_VARIABLE_COUNT] {
        self.affine_projective_indices
    }

    pub fn generators(&self) -> &[QuadraticPolynomialA4] {
        &self.generators
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TogliattiProjectiveSupportGroebnerCertificate {
    support: TogliattiProjectiveSupport,
    certificate: GroebnerCertificate<TOGLIATTI_PROJECTIVE_STRATUM_VARIABLE_COUNT, BigRational>,
}

impl TogliattiProjectiveSupportGroebnerCertificate {
    pub fn support(&self) -> TogliattiProjectiveSupport {
        self.support
    }

    pub fn certificate(
        &self,
    ) -> &GroebnerCertificate<TOGLIATTI_PROJECTIVE_STRATUM_VARIABLE_COUNT, BigRational> {
        &self.certificate
    }

    pub fn expected_generators(&self) -> Vec<BigPolynomialA4> {
        togliatti_projective_support_stratum_generators(self.support.mask())
            .generators
            .into_iter()
            .map(rational_stratum_polynomial_to_big_rational)
            .collect()
    }

    pub fn expected_quotient_length(&self) -> usize {
        TOGLIATTI_PROJECTIVE_SUPPORT_STRATUM_LENGTHS[usize::from(self.support.mask() - 1)]
    }

    pub fn generators_match_model(&self) -> bool {
        self.certificate.generators() == self.expected_generators().as_slice()
    }

    pub fn verify(&self) -> TogliattiProjectiveSupportGroebnerVerification {
        let groebner_verification = self.certificate.verify();
        TogliattiProjectiveSupportGroebnerVerification {
            support: self.support,
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
pub struct TogliattiProjectiveSupportGroebnerVerification {
    support: TogliattiProjectiveSupport,
    order: MonomialOrder,
    generators_match_model: bool,
    basis_is_groebner: bool,
    generators_reduce_to_zero: bool,
    basis_size: usize,
    quotient_dimension: Option<usize>,
    expected_quotient_length: usize,
}

impl TogliattiProjectiveSupportGroebnerVerification {
    pub fn support(self) -> TogliattiProjectiveSupport {
        self.support
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
pub struct TogliattiSingularSchemeCertificate {
    support_strata: Vec<TogliattiProjectiveSupportGroebnerCertificate>,
}

impl TogliattiSingularSchemeCertificate {
    pub fn support_strata(&self) -> &[TogliattiProjectiveSupportGroebnerCertificate] {
        &self.support_strata
    }

    pub fn verified_projective_length(&self) -> Option<usize> {
        let chart_zero = togliatti_affine_chart_grevlex_certificate(0).ok()?;
        let chart_zero_verification = chart_zero.verify();
        if !chart_zero_verification.verified() {
            return None;
        }

        let mut nonzero_support_length = 0;
        for stratum in &self.support_strata {
            if stratum.expected_quotient_length() == 0 {
                let verification = stratum.verify();
                if !verification.verified() {
                    return None;
                }
            } else {
                nonzero_support_length += stratum.expected_quotient_length();
            }
        }

        (chart_zero_verification.quotient_dimension() == Some(nonzero_support_length))
            .then_some(nonzero_support_length)
    }

    pub fn support_lengths(&self) -> Vec<(u8, usize)> {
        self.support_strata
            .iter()
            .map(|stratum| (stratum.support().mask(), stratum.expected_quotient_length()))
            .collect()
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SpecialTogliattiSingularSchemeCertificate {
    affine_chart3: SpecialTogliattiAffineChartGroebnerCertificate,
    affine_chart3_lift: QuadraticGroebnerLiftCertificate<AFFINE_P3_VARIABLE_COUNT>,
    hessian_degenerate: SpecialTogliattiHessianDegenerateGroebnerCertificate,
    hessian_degenerate_lift: QuadraticGroebnerLiftCertificate<AFFINE_P3_VARIABLE_COUNT>,
    infinity_support_strata: Vec<SpecialTogliattiInfinitySupportGroebnerCertificate>,
    infinity_support_lifts:
        Vec<QuadraticGroebnerLiftCertificate<TOGLIATTI_PROJECTIVE_STRATUM_VARIABLE_COUNT>>,
}

impl SpecialTogliattiSingularSchemeCertificate {
    pub fn affine_chart3(&self) -> &SpecialTogliattiAffineChartGroebnerCertificate {
        &self.affine_chart3
    }

    pub fn affine_chart3_lift(
        &self,
    ) -> &QuadraticGroebnerLiftCertificate<AFFINE_P3_VARIABLE_COUNT> {
        &self.affine_chart3_lift
    }

    pub fn hessian_degenerate(&self) -> &SpecialTogliattiHessianDegenerateGroebnerCertificate {
        &self.hessian_degenerate
    }

    pub fn hessian_degenerate_lift(
        &self,
    ) -> &QuadraticGroebnerLiftCertificate<AFFINE_P3_VARIABLE_COUNT> {
        &self.hessian_degenerate_lift
    }

    pub fn infinity_support_strata(&self) -> &[SpecialTogliattiInfinitySupportGroebnerCertificate] {
        &self.infinity_support_strata
    }

    pub fn infinity_support_lifts(
        &self,
    ) -> &[QuadraticGroebnerLiftCertificate<TOGLIATTI_PROJECTIVE_STRATUM_VARIABLE_COUNT>] {
        &self.infinity_support_lifts
    }

    pub fn verified_projective_length(&self) -> Option<usize> {
        let affine_verification = self.affine_chart3.verify();
        if !affine_verification.verified() {
            return None;
        }
        if !self.affine_chart3_lift.verifies_quadratic_targets(
            self.affine_chart3.certificate().generators(),
            self.affine_chart3.certificate().basis(),
        ) {
            return None;
        }

        if self.infinity_support_strata.len() != self.infinity_support_lifts.len() {
            return None;
        }
        for (stratum, lift) in self
            .infinity_support_strata
            .iter()
            .zip(&self.infinity_support_lifts)
        {
            if !stratum.verify().verified_empty() {
                return None;
            }
            if !lift.verifies_quadratic_targets(
                stratum.certificate().generators(),
                stratum.certificate().basis(),
            ) {
                return None;
            }
        }

        affine_verification.quotient_dimension()
    }

    pub fn verified_reduced_ordinary_node_count(&self) -> Option<usize> {
        let projective_length = self.verified_projective_length()?;
        if self.hessian_degenerate.verify().verified_empty()
            && self.hessian_degenerate_lift.verifies_quadratic_targets(
                self.hessian_degenerate.certificate().generators(),
                self.hessian_degenerate.certificate().basis(),
            )
        {
            Some(projective_length)
        } else {
            None
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SpecialTogliattiAffineChartGroebnerCertificate {
    certificate: GroebnerCertificate<AFFINE_P3_VARIABLE_COUNT, QuadraticRational>,
}

impl SpecialTogliattiAffineChartGroebnerCertificate {
    pub fn chart_variable(&self) -> usize {
        3
    }

    pub fn certificate(&self) -> &GroebnerCertificate<AFFINE_P3_VARIABLE_COUNT, QuadraticRational> {
        &self.certificate
    }

    pub fn expected_generators(&self) -> Vec<QuadraticPolynomialA3> {
        special_togliatti_affine_chart_generators(3)
    }

    pub fn generators_match_model(&self) -> bool {
        self.certificate.generators() == self.expected_generators().as_slice()
    }

    pub fn verify(&self) -> SpecialTogliattiAffineChartGroebnerVerification {
        let groebner_verification = self.certificate.verify();
        SpecialTogliattiAffineChartGroebnerVerification {
            generators_match_model: self.generators_match_model(),
            basis_is_groebner: groebner_verification.basis_is_groebner(),
            generators_reduce_to_zero: groebner_verification.generators_reduce_to_zero(),
            quotient_dimension: self.certificate.quotient_dimension(),
            basis_size: self.certificate.basis().len(),
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct SpecialTogliattiAffineChartGroebnerVerification {
    generators_match_model: bool,
    basis_is_groebner: bool,
    generators_reduce_to_zero: bool,
    quotient_dimension: Option<usize>,
    basis_size: usize,
}

impl SpecialTogliattiAffineChartGroebnerVerification {
    pub fn generators_match_model(self) -> bool {
        self.generators_match_model
    }

    pub fn basis_is_groebner(self) -> bool {
        self.basis_is_groebner
    }

    pub fn generators_reduce_to_zero(self) -> bool {
        self.generators_reduce_to_zero
    }

    pub fn quotient_dimension(self) -> Option<usize> {
        self.quotient_dimension
    }

    pub fn basis_size(self) -> usize {
        self.basis_size
    }

    pub fn verified(self) -> bool {
        self.generators_match_model
            && self.basis_is_groebner
            && self.generators_reduce_to_zero
            && self.quotient_dimension == Some(SPECIAL_TOGLIATTI_AFFINE_CHART3_QUOTIENT_LENGTH)
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SpecialTogliattiHessianDegenerateGroebnerCertificate {
    certificate: GroebnerCertificate<AFFINE_P3_VARIABLE_COUNT, QuadraticRational>,
}

impl SpecialTogliattiHessianDegenerateGroebnerCertificate {
    pub fn chart_variable(&self) -> usize {
        3
    }

    pub fn certificate(&self) -> &GroebnerCertificate<AFFINE_P3_VARIABLE_COUNT, QuadraticRational> {
        &self.certificate
    }

    pub fn expected_generators(&self) -> Vec<QuadraticPolynomialA3> {
        special_togliatti_affine_chart3_hessian_degenerate_generators()
    }

    pub fn generators_match_model(&self) -> bool {
        self.certificate.generators() == self.expected_generators().as_slice()
    }

    pub fn verify(&self) -> SpecialTogliattiHessianDegenerateGroebnerVerification {
        let groebner_verification = self.certificate.verify();
        SpecialTogliattiHessianDegenerateGroebnerVerification {
            generators_match_model: self.generators_match_model(),
            basis_is_groebner: groebner_verification.basis_is_groebner(),
            generators_reduce_to_zero: groebner_verification.generators_reduce_to_zero(),
            quotient_dimension: self.certificate.quotient_dimension(),
            basis_size: self.certificate.basis().len(),
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct SpecialTogliattiHessianDegenerateGroebnerVerification {
    generators_match_model: bool,
    basis_is_groebner: bool,
    generators_reduce_to_zero: bool,
    quotient_dimension: Option<usize>,
    basis_size: usize,
}

impl SpecialTogliattiHessianDegenerateGroebnerVerification {
    pub fn generators_match_model(self) -> bool {
        self.generators_match_model
    }

    pub fn basis_is_groebner(self) -> bool {
        self.basis_is_groebner
    }

    pub fn generators_reduce_to_zero(self) -> bool {
        self.generators_reduce_to_zero
    }

    pub fn quotient_dimension(self) -> Option<usize> {
        self.quotient_dimension
    }

    pub fn basis_size(self) -> usize {
        self.basis_size
    }

    pub fn verified_empty(self) -> bool {
        self.generators_match_model
            && self.basis_is_groebner
            && self.generators_reduce_to_zero
            && self.quotient_dimension == Some(SPECIAL_TOGLIATTI_HESSIAN_BAD_QUOTIENT_LENGTH)
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SpecialTogliattiInfinitySupportGroebnerCertificate {
    support: TogliattiProjectiveSupport,
    certificate:
        GroebnerCertificate<TOGLIATTI_PROJECTIVE_STRATUM_VARIABLE_COUNT, QuadraticRational>,
}

impl SpecialTogliattiInfinitySupportGroebnerCertificate {
    pub fn support(&self) -> TogliattiProjectiveSupport {
        self.support
    }

    pub fn certificate(
        &self,
    ) -> &GroebnerCertificate<TOGLIATTI_PROJECTIVE_STRATUM_VARIABLE_COUNT, QuadraticRational> {
        &self.certificate
    }

    pub fn expected_generators(&self) -> Vec<QuadraticPolynomialA4> {
        special_togliatti_infinity_support_stratum_generators(self.support.mask()).generators
    }

    pub fn generators_match_model(&self) -> bool {
        self.certificate.generators() == self.expected_generators().as_slice()
    }

    pub fn verify(&self) -> SpecialTogliattiInfinitySupportGroebnerVerification {
        let groebner_verification = self.certificate.verify();
        SpecialTogliattiInfinitySupportGroebnerVerification {
            support: self.support,
            generators_match_model: self.generators_match_model(),
            basis_is_groebner: groebner_verification.basis_is_groebner(),
            generators_reduce_to_zero: groebner_verification.generators_reduce_to_zero(),
            quotient_dimension: self.certificate.quotient_dimension(),
            basis_size: self.certificate.basis().len(),
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct SpecialTogliattiInfinitySupportGroebnerVerification {
    support: TogliattiProjectiveSupport,
    generators_match_model: bool,
    basis_is_groebner: bool,
    generators_reduce_to_zero: bool,
    quotient_dimension: Option<usize>,
    basis_size: usize,
}

impl SpecialTogliattiInfinitySupportGroebnerVerification {
    pub fn support(self) -> TogliattiProjectiveSupport {
        self.support
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

    pub fn quotient_dimension(self) -> Option<usize> {
        self.quotient_dimension
    }

    pub fn basis_size(self) -> usize {
        self.basis_size
    }

    pub fn verified_empty(self) -> bool {
        self.generators_match_model
            && self.basis_is_groebner
            && self.generators_reduce_to_zero
            && self.quotient_dimension == Some(0)
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TogliattiAffineChartGroebnerCertificate {
    chart_variable: usize,
    projective_variable_indices: [usize; AFFINE_P3_VARIABLE_COUNT],
    certificate: GroebnerCertificate<AFFINE_P3_VARIABLE_COUNT, BigRational>,
}

impl TogliattiAffineChartGroebnerCertificate {
    pub fn chart_variable(&self) -> usize {
        self.chart_variable
    }

    pub fn projective_variable_indices(&self) -> [usize; AFFINE_P3_VARIABLE_COUNT] {
        self.projective_variable_indices
    }

    pub fn certificate(&self) -> &GroebnerCertificate<AFFINE_P3_VARIABLE_COUNT, BigRational> {
        &self.certificate
    }

    pub fn expected_generators(&self) -> Vec<BigPolynomialA3> {
        togliatti_affine_chart_generators(self.chart_variable)
            .into_iter()
            .map(rational_polynomial_to_big_rational)
            .collect()
    }

    pub fn generators_match_model(&self) -> bool {
        self.certificate.generators() == self.expected_generators().as_slice()
    }

    pub fn verify(&self) -> TogliattiAffineChartGroebnerVerification {
        let groebner_verification = self.certificate.verify();
        TogliattiAffineChartGroebnerVerification {
            chart_variable: self.chart_variable,
            projective_variable_indices: self.projective_variable_indices,
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
pub struct TogliattiAffineChartGroebnerVerification {
    chart_variable: usize,
    projective_variable_indices: [usize; AFFINE_P3_VARIABLE_COUNT],
    order: MonomialOrder,
    generators_match_model: bool,
    basis_is_groebner: bool,
    generators_reduce_to_zero: bool,
    basis_size: usize,
    quotient_dimension: Option<usize>,
}

impl TogliattiAffineChartGroebnerVerification {
    pub fn chart_variable(self) -> usize {
        self.chart_variable
    }

    pub fn projective_variable_indices(self) -> [usize; AFFINE_P3_VARIABLE_COUNT] {
        self.projective_variable_indices
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

    pub fn verified(self) -> bool {
        self.generators_match_model
            && self.basis_is_groebner
            && self.generators_reduce_to_zero
            && self.quotient_dimension == Some(TOGLIATTI_AFFINE_CHART_QUOTIENT_LENGTH)
    }
}

fn togliatti_determinant_polynomial() -> PolynomialP3 {
    let [x, y, z, w] = variables();
    let s1 = x.add(&y).add(&z).add(&w);
    let s3 = x
        .pow_usize(3)
        .add(&y.pow_usize(3))
        .add(&z.pow_usize(3))
        .add(&w.pow_usize(3));

    let a = x.scale(q(32)).add(&z.scale(q(-24))).add(&w.scale(q(15)));
    let b = x.scale(q(2)).add(&z.scale(q(-7))).add(&w.scale(q(-3)));
    let d = z.scale(q(-4)).add(&w.scale(q(-3)));
    let m13 = x
        .pow_usize(2)
        .scale(q(9))
        .add(&y.pow_usize(2).scale(q(7)))
        .add(&z.pow_usize(2).scale(q(5)))
        .add(&w.pow_usize(2).scale(q(-8)))
        .sub(&s1.pow_usize(2).scale(r(7, 2)));
    let m23 = x
        .pow_usize(2)
        .scale(q(2))
        .add(&y.pow_usize(2).scale(q(2)))
        .sub(&w.pow_usize(2))
        .sub(&s1.pow_usize(2));
    let f = s3.sub(&s1.pow_usize(3).scale(r(1, 4))).scale(r(1, 3));

    // For a symmetric matrix [[a,b,c],[b,d,e],[c,e,f]]:
    // det = adf + 2bce - ae^2 - dc^2 - fb^2.
    a.mul(&d)
        .mul(&f)
        .add(&b.mul(&m13).mul(&m23).scale(q(2)))
        .sub(&a.mul(&m23.pow_usize(2)))
        .sub(&d.mul(&m13.pow_usize(2)))
        .sub(&f.mul(&b.pow_usize(2)))
}

fn special_togliatti_polynomial() -> QuadraticPolynomialP3 {
    let [x, y, z, w] = quadratic_variables();
    let sqrt_five = QuadraticRational::sqrt(5);
    let b = QuadraticRational::new(r(-1, 4), r(1, 20), 5);
    let d = -QuadraticRational::ONE - sqrt_five;

    let p = x
        .pow_usize(5)
        .add(&x.pow_usize(4).mul(&w).scale(qq(-5)))
        .sub(&x.pow_usize(3).mul(&y.pow_usize(2)).scale(qq(10)))
        .sub(&x.pow_usize(2).mul(&y.pow_usize(2)).mul(&w).scale(qq(10)))
        .add(&x.pow_usize(2).mul(&w.pow_usize(3)).scale(qq(20)))
        .add(&x.mul(&y.pow_usize(4)).scale(qq(5)))
        .sub(&y.pow_usize(4).mul(&w).scale(qq(5)))
        .add(&y.pow_usize(2).mul(&w.pow_usize(3)).scale(qq(20)))
        .sub(&w.pow_usize(5).scale(qq(16)));
    let q = x
        .pow_usize(2)
        .add(&y.pow_usize(2))
        .add(&z.pow_usize(2).scale(b))
        .add(&z.mul(&w))
        .add(&w.pow_usize(2).scale(d));

    p.scale(qq(2)).add(&z.mul(&q.pow_usize(2)).scale(qq(5)))
}

fn affine_hessian_determinant(polynomial: &QuadraticPolynomialA3) -> QuadraticPolynomialA3 {
    let h = std::array::from_fn::<_, AFFINE_P3_VARIABLE_COUNT, _>(|row| {
        std::array::from_fn::<_, AFFINE_P3_VARIABLE_COUNT, _>(|col| {
            polynomial.partial_derivative(row).partial_derivative(col)
        })
    });

    h[0][0]
        .mul(&h[1][1])
        .mul(&h[2][2])
        .add(&h[0][1].mul(&h[1][2]).mul(&h[2][0]).scale(qq(2)))
        .sub(&h[0][0].mul(&h[1][2].pow_usize(2)))
        .sub(&h[1][1].mul(&h[0][2].pow_usize(2)))
        .sub(&h[2][2].mul(&h[0][1].pow_usize(2)))
}

fn variables() -> [PolynomialP3; P3_VARIABLE_COUNT] {
    std::array::from_fn(PolynomialP3::variable)
}

fn quadratic_variables() -> [QuadraticPolynomialP3; P3_VARIABLE_COUNT] {
    std::array::from_fn(QuadraticPolynomialP3::variable)
}

fn q(value: i64) -> Rational {
    Rational::from_i64(value)
}

fn r(numerator: i64, denominator: i64) -> Rational {
    Rational::new(numerator.into(), denominator.into())
}

fn qq(value: i64) -> QuadraticRational {
    QuadraticRational::from_i64(value)
}

fn rational_polynomial_to_big_rational(polynomial: PolynomialA3) -> BigPolynomialA3 {
    polynomial.map_coefficients(|coefficient| BigRational::from(*coefficient))
}

fn rational_stratum_polynomial_to_big_rational(polynomial: PolynomialA4) -> BigPolynomialA4 {
    polynomial.map_coefficients(|coefficient| BigRational::from(*coefficient))
}

fn lift_affine3_polynomial_to_stratum(polynomial: PolynomialA3) -> PolynomialA4 {
    PolynomialA4::from_terms(
        polynomial
            .terms()
            .into_iter()
            .map(|term| {
                let affine_exponents = term.exponents();
                let exponents = std::array::from_fn(|index| {
                    if index < AFFINE_P3_VARIABLE_COUNT {
                        affine_exponents[index]
                    } else {
                        0
                    }
                });
                (term.coefficient(), exponents)
            })
            .collect(),
    )
}

fn lift_quadratic_affine3_polynomial_to_stratum(
    polynomial: QuadraticPolynomialA3,
) -> QuadraticPolynomialA4 {
    QuadraticPolynomialA4::from_terms(
        polynomial
            .terms()
            .into_iter()
            .map(|term| {
                let affine_exponents = term.exponents();
                let exponents = std::array::from_fn(|index| {
                    if index < AFFINE_P3_VARIABLE_COUNT {
                        affine_exponents[index]
                    } else {
                        0
                    }
                });
                (term.coefficient(), exponents)
            })
            .collect(),
    )
}

#[cfg(test)]
mod tests {
    use super::{
        TOGLIATTI_PROJECTIVE_SUPPORT_STRATUM_LENGTHS, beauville_maximum_node_count,
        special_togliatti_affine_chart3_grevlex_certificate,
        special_togliatti_affine_chart3_grevlex_lift_certificate,
        special_togliatti_affine_chart3_hessian_degenerate_generators,
        special_togliatti_hessian_degenerate_grevlex_certificate,
        special_togliatti_hessian_degenerate_grevlex_lift_certificate,
        special_togliatti_infinity_support_grevlex_certificates,
        special_togliatti_infinity_support_grevlex_lift_certificates,
        special_togliatti_quintic_polynomial, special_togliatti_singular_scheme_certificate,
        togliatti_affine_chart_generators, togliatti_affine_chart_grevlex_certificates,
        togliatti_affine_chart_variable_indices, togliatti_literature_node_count,
        togliatti_matrix_entry_degrees, togliatti_projective_support_grevlex_certificates,
        togliatti_quintic, togliatti_singular_scheme_certificate,
    };
    use nodal_core::{MonomialOrder, ProjectivePoint, Rational};

    #[test]
    fn togliatti_quintic_has_degree_five() {
        let surface = togliatti_quintic();

        assert_eq!(surface.polynomial().degree(), 5);
        assert_eq!(surface.polynomial().terms().len(), 55);
    }

    #[test]
    fn determinant_entries_have_expected_degrees() {
        assert_eq!(
            togliatti_matrix_entry_degrees(),
            [[1, 1, 2], [1, 1, 2], [2, 2, 3]]
        );
    }

    #[test]
    fn special_togliatti_quintic_has_degree_five() {
        let polynomial = special_togliatti_quintic_polynomial();

        assert_eq!(polynomial.degree(), 5);
        assert_eq!(polynomial.terms().len(), 23);
    }

    #[test]
    fn literature_node_count_matches_beauville_bound() {
        assert_eq!(togliatti_literature_node_count(), 31);
        assert_eq!(beauville_maximum_node_count(), 31);
    }

    #[test]
    fn a_general_point_is_not_singular() {
        let surface = togliatti_quintic();
        let point = ProjectivePoint::new(vec![1.into(), 1.into(), 1.into(), 1.into()]);

        assert!(!surface.polynomial().is_singular_at(&point));
        assert!(!surface.polynomial().is_ordinary_double_point_at(&point));
    }

    #[test]
    fn determinant_value_at_a_sample_point_is_stable() {
        let surface = togliatti_quintic();
        let coords = [1.into(), 2.into(), 3.into(), 4.into()];

        assert_eq!(
            surface.polynomial().evaluate(&coords),
            Rational::from_i64(1_008_402)
        );
    }

    #[test]
    fn affine_chart_generators_match_the_projective_quintic() {
        let surface = togliatti_quintic();
        let generators = togliatti_affine_chart_generators(3);
        let affine_coords = [1.into(), 2.into(), 3.into()];
        let projective_coords = [1.into(), 2.into(), 3.into(), 1.into()];

        assert_eq!(generators.len(), 4);
        assert_eq!(generators[0].degree(), 5);
        assert_eq!(generators[1].degree(), 4);
        assert_eq!(generators[2].degree(), 4);
        assert_eq!(generators[3].degree(), 4);
        assert_eq!(
            generators[0].evaluate(&affine_coords),
            surface.polynomial().evaluate(&projective_coords)
        );
    }

    #[test]
    fn all_four_togliatti_charts_have_jacobian_generators() {
        assert_eq!(togliatti_affine_chart_variable_indices(0), [1, 2, 3]);
        assert_eq!(togliatti_affine_chart_variable_indices(1), [0, 2, 3]);
        assert_eq!(togliatti_affine_chart_variable_indices(2), [0, 1, 3]);
        assert_eq!(togliatti_affine_chart_variable_indices(3), [0, 1, 2]);

        for chart_variable in 0..4 {
            let generators = togliatti_affine_chart_generators(chart_variable);

            assert_eq!(generators.len(), 4);
            assert_eq!(generators[0].degree(), 5);
            assert!(
                generators[1..]
                    .iter()
                    .all(|generator| generator.degree() <= 4)
            );
        }
    }

    #[test]
    fn all_chart_grevlex_certificates_match_current_generators() {
        let certificates = togliatti_affine_chart_grevlex_certificates()
            .expect("all affine chart certificates parse");
        let expected_basis_sizes = [8, 8, 9, 9];

        for (certificate, expected_basis_size) in certificates.iter().zip(expected_basis_sizes) {
            assert_eq!(certificate.certificate().order(), MonomialOrder::GrevLex);
            assert!(certificate.generators_match_model());
            assert_eq!(certificate.certificate().basis().len(), expected_basis_size);
            assert_eq!(certificate.certificate().quotient_dimension(), Some(16));
        }
    }

    #[test]
    fn all_chart_grevlex_certificates_verify_in_rust() {
        let certificates = togliatti_affine_chart_grevlex_certificates()
            .expect("all affine chart certificates parse");

        for certificate in certificates {
            let verification = certificate.verify();
            assert_eq!(verification.order(), MonomialOrder::GrevLex);
            assert!(verification.generators_match_model());
            assert!(verification.basis_is_groebner());
            assert!(verification.generators_reduce_to_zero());
            assert_eq!(verification.quotient_dimension(), Some(16));
            assert!(verification.verified());
        }
    }

    #[test]
    fn projective_support_strata_certificates_match_current_generators() {
        let certificates = togliatti_projective_support_grevlex_certificates()
            .expect("all support stratum certificates parse");

        assert_eq!(certificates.len(), 15);
        assert_eq!(
            TOGLIATTI_PROJECTIVE_SUPPORT_STRATUM_LENGTHS
                .into_iter()
                .sum::<usize>(),
            16
        );

        for certificate in certificates {
            assert_eq!(certificate.certificate().order(), MonomialOrder::GrevLex);
            assert!(certificate.generators_match_model());
            assert_eq!(
                certificate.certificate().quotient_dimension(),
                Some(certificate.expected_quotient_length())
            );
        }
    }

    #[test]
    fn projective_support_strata_empty_boundary_certificates_verify_in_rust() {
        let certificate =
            togliatti_singular_scheme_certificate().expect("support strata certificates parse");

        for stratum in certificate.support_strata() {
            if stratum.expected_quotient_length() != 0 {
                continue;
            }

            let verification = stratum.verify();
            assert_eq!(verification.order(), MonomialOrder::GrevLex);
            assert!(verification.generators_match_model());
            assert!(verification.basis_is_groebner());
            assert!(verification.generators_reduce_to_zero());
            assert_eq!(
                verification.quotient_dimension(),
                Some(verification.expected_quotient_length())
            );
            assert!(verification.verified());
        }

        assert_eq!(certificate.support_lengths().last(), Some(&(15, 16)));
        assert_ne!(16, togliatti_literature_node_count());
    }

    #[test]
    fn special_togliatti_chart3_certificate_matches_current_generators() {
        let certificate = special_togliatti_affine_chart3_grevlex_certificate()
            .expect("special Togliatti chart certificate parses");

        assert_eq!(certificate.chart_variable(), 3);
        assert_eq!(certificate.certificate().order(), MonomialOrder::GrevLex);
        assert_eq!(certificate.certificate().basis().len(), 15);
        assert_eq!(certificate.certificate().quotient_dimension(), Some(31));
        assert!(certificate.generators_match_model());
    }

    #[test]
    fn special_togliatti_chart3_certificate_verifies_in_rust() {
        let certificate = special_togliatti_affine_chart3_grevlex_certificate()
            .expect("special Togliatti chart certificate parses");

        let verification = certificate.verify();
        assert!(verification.generators_match_model());
        assert!(verification.basis_is_groebner());
        assert!(verification.generators_reduce_to_zero());
        assert_eq!(verification.basis_size(), 15);
        assert_eq!(verification.quotient_dimension(), Some(31));
        assert!(verification.verified());
    }

    #[test]
    fn special_togliatti_chart3_lift_certificate_verifies_basis_membership() {
        let certificate = special_togliatti_affine_chart3_grevlex_certificate()
            .expect("special Togliatti chart certificate parses");
        let lift = special_togliatti_affine_chart3_grevlex_lift_certificate()
            .expect("special Togliatti chart lift parses");

        assert_eq!(
            lift.source_count(),
            certificate.certificate().generators().len()
        );
        assert_eq!(lift.target_count(), certificate.certificate().basis().len());
        assert!(lift.verifies_quadratic_targets(
            certificate.certificate().generators(),
            certificate.certificate().basis()
        ));
    }

    #[test]
    fn special_togliatti_hessian_bad_generators_extend_chart3_jacobian() {
        let generators = special_togliatti_affine_chart3_hessian_degenerate_generators();

        assert_eq!(generators.len(), 5);
        assert_eq!(generators[0].degree(), 5);
        assert!(
            generators[1..4]
                .iter()
                .all(|generator| generator.degree() <= 4)
        );
        assert_eq!(generators[4].degree(), 9);
    }

    #[test]
    fn special_togliatti_hessian_bad_certificate_verifies_empty() {
        let certificate = special_togliatti_hessian_degenerate_grevlex_certificate()
            .expect("special Togliatti Hessian-bad certificate parses");

        assert_eq!(certificate.chart_variable(), 3);
        assert_eq!(certificate.certificate().order(), MonomialOrder::GrevLex);
        assert_eq!(certificate.certificate().basis().len(), 1);
        assert_eq!(certificate.certificate().quotient_dimension(), Some(0));
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
    fn special_togliatti_hessian_bad_lift_certificate_verifies_unit_membership() {
        let certificate = special_togliatti_hessian_degenerate_grevlex_certificate()
            .expect("special Togliatti Hessian-bad certificate parses");
        let lift = special_togliatti_hessian_degenerate_grevlex_lift_certificate()
            .expect("special Togliatti Hessian-bad lift parses");

        assert_eq!(
            lift.source_count(),
            certificate.certificate().generators().len()
        );
        assert_eq!(lift.target_count(), certificate.certificate().basis().len());
        assert!(lift.verifies_quadratic_targets(
            certificate.certificate().generators(),
            certificate.certificate().basis()
        ));
    }

    #[test]
    fn special_togliatti_infinity_support_certificates_verify_empty() {
        let certificates = special_togliatti_infinity_support_grevlex_certificates()
            .expect("special Togliatti infinity support certificates parse");

        assert_eq!(certificates.len(), 7);
        for certificate in certificates {
            let verification = certificate.verify();
            assert!(verification.generators_match_model());
            assert!(verification.basis_is_groebner());
            assert!(verification.generators_reduce_to_zero());
            assert_eq!(verification.basis_size(), 1);
            assert_eq!(verification.quotient_dimension(), Some(0));
            assert!(verification.verified_empty());
        }
    }

    #[test]
    fn special_togliatti_infinity_support_lifts_verify_unit_membership() {
        let certificates = special_togliatti_infinity_support_grevlex_certificates()
            .expect("special Togliatti infinity support certificates parse");
        let lifts = special_togliatti_infinity_support_grevlex_lift_certificates()
            .expect("special Togliatti infinity support lift certificates parse");

        assert_eq!(certificates.len(), lifts.len());
        for (certificate, lift) in certificates.iter().zip(&lifts) {
            assert_eq!(
                lift.source_count(),
                certificate.certificate().generators().len()
            );
            assert_eq!(lift.target_count(), certificate.certificate().basis().len());
            assert!(lift.verifies_quadratic_targets(
                certificate.certificate().generators(),
                certificate.certificate().basis()
            ));
        }
    }

    #[test]
    fn special_togliatti_projective_certificate_has_length_thirty_one() {
        let certificate = special_togliatti_singular_scheme_certificate()
            .expect("special Togliatti projective certificates parse");

        assert_eq!(certificate.infinity_support_strata().len(), 7);
        assert_eq!(certificate.infinity_support_lifts().len(), 7);
        assert!(certificate.affine_chart3_lift().verifies_quadratic_targets(
            certificate.affine_chart3().certificate().generators(),
            certificate.affine_chart3().certificate().basis()
        ));
        assert!(certificate.hessian_degenerate().verify().verified_empty());
        assert!(
            certificate
                .hessian_degenerate_lift()
                .verifies_quadratic_targets(
                    certificate.hessian_degenerate().certificate().generators(),
                    certificate.hessian_degenerate().certificate().basis()
                )
        );
        assert_eq!(certificate.verified_projective_length(), Some(31));
        assert_eq!(certificate.verified_reduced_ordinary_node_count(), Some(31));
        assert_eq!(
            certificate.verified_reduced_ordinary_node_count(),
            Some(togliatti_literature_node_count())
        );
    }
}
