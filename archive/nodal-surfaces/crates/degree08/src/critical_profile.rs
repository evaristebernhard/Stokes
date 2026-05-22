use super::{Fp, PolynomialP3Fp};
use nodal_core::{FieldElement, Matrix, P3_VARIABLE_COUNT, SparsePolynomial};
use std::collections::BTreeMap;

pub type AffinePlanePolynomialFp<const P: i64> = SparsePolynomial<Fp<P>, 2>;
pub type AffineLineFp<const P: i64> = [Fp<P>; 3];

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct AffineLineArrangementFp<const P: i64> {
    lines: Vec<AffineLineFp<P>>,
}

impl<const P: i64> AffineLineArrangementFp<P> {
    pub fn new(lines: Vec<AffineLineFp<P>>) -> Self {
        assert!(!lines.is_empty(), "line arrangement cannot be empty");
        Self { lines }
    }

    pub fn normal_form10(params: [i64; 10]) -> Self {
        let mut lines = vec![
            [Fp::one(), Fp::zero(), Fp::zero()],
            [Fp::zero(), Fp::one(), Fp::zero()],
            [-Fp::one(), -Fp::one(), Fp::one()],
        ];

        for index in 0..5 {
            let r = Fp::new(params[index]);
            let s = Fp::new(params[index + 5]);
            lines.push([s * r, s, Fp::one()]);
        }

        Self::new(lines)
    }

    pub fn normal_form10_from_slice(params: &[i64]) -> Result<Self, String> {
        let params: [i64; 10] = params.try_into().map_err(|_| {
            format!(
                "normal10 expects exactly 10 parameters: got {}",
                params.len()
            )
        })?;
        Ok(Self::normal_form10(params))
    }

    pub fn lines(&self) -> &[AffineLineFp<P>] {
        &self.lines
    }

    pub fn quality(&self) -> AffineLineArrangementQuality {
        affine_line_arrangement_quality(&self.lines)
    }

    pub fn line_product_polynomial(&self) -> AffinePlanePolynomialFp<P> {
        line_product_polynomial(&self.lines)
    }

    pub fn critical_value_profile_fast(&self) -> CriticalValueProfile<P> {
        critical_value_profile_for_lines_fast(&self.lines)
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct AffineCriticalPointFp<const P: i64> {
    point: [Fp<P>; 2],
    value: Fp<P>,
    hessian_rank: usize,
}

impl<const P: i64> AffineCriticalPointFp<P> {
    pub fn point(&self) -> [Fp<P>; 2] {
        self.point
    }

    pub fn value(&self) -> Fp<P> {
        self.value
    }

    pub fn hessian_rank(&self) -> usize {
        self.hessian_rank
    }

    pub fn is_morse(&self) -> bool {
        self.hessian_rank == 2
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CriticalValueBucket<const P: i64> {
    value: Fp<P>,
    morse_count: usize,
    degenerate_count: usize,
}

impl<const P: i64> CriticalValueBucket<P> {
    fn new(value: Fp<P>) -> Self {
        Self {
            value,
            morse_count: 0,
            degenerate_count: 0,
        }
    }

    pub fn value(&self) -> Fp<P> {
        self.value
    }

    pub fn morse_count(&self) -> usize {
        self.morse_count
    }

    pub fn degenerate_count(&self) -> usize {
        self.degenerate_count
    }

    pub fn total_count(&self) -> usize {
        self.morse_count + self.degenerate_count
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CriticalValueProfile<const P: i64> {
    points: Vec<AffineCriticalPointFp<P>>,
    buckets: BTreeMap<i64, CriticalValueBucket<P>>,
}

impl<const P: i64> CriticalValueProfile<P> {
    fn new(points: Vec<AffineCriticalPointFp<P>>) -> Self {
        let mut buckets = BTreeMap::new();
        for point in &points {
            let bucket = buckets
                .entry(point.value.value())
                .or_insert_with(|| CriticalValueBucket::new(point.value));
            if point.is_morse() {
                bucket.morse_count += 1;
            } else {
                bucket.degenerate_count += 1;
            }
        }

        Self { points, buckets }
    }

    pub fn points(&self) -> &[AffineCriticalPointFp<P>] {
        &self.points
    }

    pub fn buckets(&self) -> &BTreeMap<i64, CriticalValueBucket<P>> {
        &self.buckets
    }

    pub fn bucket(&self, value: Fp<P>) -> Option<&CriticalValueBucket<P>> {
        self.buckets.get(&value.value())
    }

    pub fn total_critical(&self) -> usize {
        self.points.len()
    }

    pub fn morse_critical(&self) -> usize {
        self.points.iter().filter(|point| point.is_morse()).count()
    }

    pub fn degenerate_critical(&self) -> usize {
        self.total_critical() - self.morse_critical()
    }

    pub fn best_weighted_pairs(&self, limit: usize) -> Vec<WeightedCriticalPair<P>> {
        let mut pairs = Vec::new();
        for primary in self.buckets.values() {
            for secondary in self.buckets.values() {
                if primary.value == secondary.value {
                    continue;
                }
                let predicted_nodes = 4 * primary.morse_count + 3 * secondary.morse_count;
                let selected_degenerate = primary.degenerate_count + secondary.degenerate_count;
                pairs.push(WeightedCriticalPair {
                    primary_value: primary.value,
                    secondary_value: secondary.value,
                    primary_morse: primary.morse_count,
                    secondary_morse: secondary.morse_count,
                    predicted_nodes,
                    selected_degenerate,
                });
            }
        }

        pairs.sort_by(|left, right| {
            right
                .predicted_nodes
                .cmp(&left.predicted_nodes)
                .then_with(|| left.selected_degenerate.cmp(&right.selected_degenerate))
                .then_with(|| right.primary_morse.cmp(&left.primary_morse))
                .then_with(|| right.secondary_morse.cmp(&left.secondary_morse))
                .then_with(|| left.primary_value.value().cmp(&right.primary_value.value()))
                .then_with(|| {
                    left.secondary_value
                        .value()
                        .cmp(&right.secondary_value.value())
                })
        });
        pairs.truncate(limit.min(pairs.len()));
        pairs
    }

    pub fn signature(&self, limit: usize) -> String {
        let mut entries = self
            .buckets
            .values()
            .map(|bucket| {
                (
                    bucket.morse_count,
                    bucket.degenerate_count,
                    bucket.value.value(),
                )
            })
            .collect::<Vec<_>>();
        entries.sort_by(|left, right| {
            right
                .0
                .cmp(&left.0)
                .then_with(|| left.1.cmp(&right.1))
                .then_with(|| left.2.cmp(&right.2))
        });
        entries
            .into_iter()
            .take(limit)
            .map(|(morse, degenerate, value)| {
                if degenerate == 0 {
                    format!("{value}:{morse}")
                } else {
                    format!("{value}:{morse}+{degenerate}d")
                }
            })
            .collect::<Vec<_>>()
            .join(",")
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct WeightedCriticalPair<const P: i64> {
    primary_value: Fp<P>,
    secondary_value: Fp<P>,
    primary_morse: usize,
    secondary_morse: usize,
    predicted_nodes: usize,
    selected_degenerate: usize,
}

impl<const P: i64> WeightedCriticalPair<P> {
    pub fn primary_value(self) -> Fp<P> {
        self.primary_value
    }

    pub fn secondary_value(self) -> Fp<P> {
        self.secondary_value
    }

    pub fn primary_morse(self) -> usize {
        self.primary_morse
    }

    pub fn secondary_morse(self) -> usize {
        self.secondary_morse
    }

    pub fn predicted_nodes(self) -> usize {
        self.predicted_nodes
    }

    pub fn selected_degenerate(self) -> usize {
        self.selected_degenerate
    }

    pub fn chebyshev_scale(self) -> Fp<P> {
        Fp::new(2) / (self.primary_value - self.secondary_value)
    }

    pub fn chebyshev_lambda(self) -> Fp<P> {
        Fp::one() - self.chebyshev_scale() * self.primary_value
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct AffineLineArrangementQuality {
    simple: bool,
    pair_count: usize,
    triple_count: usize,
    parallel_pair_count: usize,
    concurrent_triple_count: usize,
    infinity_degenerate_line_count: usize,
}

impl AffineLineArrangementQuality {
    pub fn simple(&self) -> bool {
        self.simple
    }

    pub fn pair_count(&self) -> usize {
        self.pair_count
    }

    pub fn triple_count(&self) -> usize {
        self.triple_count
    }

    pub fn parallel_pair_count(&self) -> usize {
        self.parallel_pair_count
    }

    pub fn concurrent_triple_count(&self) -> usize {
        self.concurrent_triple_count
    }

    pub fn infinity_degenerate_line_count(&self) -> usize {
        self.infinity_degenerate_line_count
    }
}

pub fn affine_plane_points<const P: i64>() -> Vec<[Fp<P>; 2]> {
    let mut points = Vec::new();
    for x in 0..P {
        for y in 0..P {
            points.push([Fp::new(x), Fp::new(y)]);
        }
    }
    points
}

pub fn critical_value_profile<const P: i64>(
    polynomial: &AffinePlanePolynomialFp<P>,
) -> CriticalValueProfile<P> {
    let gradient = [
        polynomial.partial_derivative(0),
        polynomial.partial_derivative(1),
    ];
    let hessian = [
        [
            gradient[0].partial_derivative(0),
            gradient[0].partial_derivative(1),
        ],
        [
            gradient[1].partial_derivative(0),
            gradient[1].partial_derivative(1),
        ],
    ];

    let points = affine_plane_points::<P>()
        .into_iter()
        .filter_map(|point| {
            if !gradient
                .iter()
                .all(|partial| partial.evaluate(&point).is_zero())
            {
                return None;
            }

            let hessian_rank = Matrix::from_rows(
                hessian
                    .iter()
                    .map(|row| row.iter().map(|entry| entry.evaluate(&point)).collect())
                    .collect(),
            )
            .rank();

            Some(AffineCriticalPointFp {
                point,
                value: polynomial.evaluate(&point),
                hessian_rank,
            })
        })
        .collect();

    CriticalValueProfile::new(points)
}

pub fn line_product_polynomial<const P: i64>(
    lines: &[AffineLineFp<P>],
) -> AffinePlanePolynomialFp<P> {
    let [x, y] = std::array::from_fn(AffinePlanePolynomialFp::<P>::variable);
    lines.iter().fold(
        AffinePlanePolynomialFp::<P>::constant(Fp::one()),
        |product, line| {
            let factor = x
                .scale(line[0])
                .add(&y.scale(line[1]))
                .add(&AffinePlanePolynomialFp::<P>::constant(line[2]));
            product.mul(&factor)
        },
    )
}

pub fn normal_form10_lines<const P: i64>(params: &[i64]) -> Result<Vec<AffineLineFp<P>>, String> {
    Ok(
        AffineLineArrangementFp::<P>::normal_form10_from_slice(params)?
            .lines()
            .to_vec(),
    )
}

pub fn critical_value_profile_for_lines_fast<const P: i64>(
    lines: &[AffineLineFp<P>],
) -> CriticalValueProfile<P> {
    let mut points = Vec::new();

    for x in 0..P {
        for y in 0..P {
            let point = [Fp::new(x), Fp::new(y)];
            let line_values = lines
                .iter()
                .map(|line| evaluate_affine_line(*line, point))
                .collect::<Vec<_>>();
            let value = line_values
                .iter()
                .copied()
                .fold(Fp::one(), |product, factor| product * factor);

            let mut qx = Fp::zero();
            let mut qy = Fp::zero();
            let mut qxx = Fp::zero();
            let mut qxy = Fp::zero();
            let mut qyy = Fp::zero();

            for (index, line) in lines.iter().enumerate() {
                let product = product_except(&line_values, index, None);
                qx = qx + line[0] * product;
                qy = qy + line[1] * product;
            }

            if !(qx.is_zero() && qy.is_zero()) {
                continue;
            }

            for first in 0..lines.len() {
                for second in (first + 1)..lines.len() {
                    let product = product_except(&line_values, first, Some(second));
                    qxx = qxx + Fp::new(2) * lines[first][0] * lines[second][0] * product;
                    qxy = qxy
                        + (lines[first][0] * lines[second][1] + lines[second][0] * lines[first][1])
                            * product;
                    qyy = qyy + Fp::new(2) * lines[first][1] * lines[second][1] * product;
                }
            }

            points.push(AffineCriticalPointFp {
                point,
                value,
                hessian_rank: symmetric_2x2_rank(qxx, qxy, qyy),
            });
        }
    }

    CriticalValueProfile::new(points)
}

pub fn slope_polynomial_lines<const P: i64>(coefficients: &[i64]) -> Vec<AffineLineFp<P>> {
    slope_parameters()
        .into_iter()
        .map(|slope| {
            let intercept = coefficients.iter().enumerate().fold(
                Fp::<P>::zero(),
                |sum, (index, coefficient)| {
                    sum + Fp::new(*coefficient) * Fp::new(slope).pow_usize(index + 2)
                },
            );
            [Fp::one(), Fp::new(slope), intercept]
        })
        .collect()
}

pub fn slope_parameters() -> [i64; 8] {
    [-4, -3, -2, -1, 1, 2, 3, 4]
}

pub fn affine_line_arrangement_quality<const P: i64>(
    lines: &[AffineLineFp<P>],
) -> AffineLineArrangementQuality {
    let mut parallel_pair_count = 0;
    let mut concurrent_triple_count = 0;
    let mut infinity_degenerate_line_count = 0;
    let mut pair_count = 0;
    let mut triple_count = 0;

    for line in lines {
        if line_direction_is_zero(*line) {
            infinity_degenerate_line_count += 1;
        }
    }

    for first in 0..lines.len() {
        for second in (first + 1)..lines.len() {
            pair_count += 1;
            if line_direction_determinant(lines[first], lines[second]).is_zero() {
                parallel_pair_count += 1;
            }
        }
    }

    for first in 0..lines.len() {
        for second in (first + 1)..lines.len() {
            for third in (second + 1)..lines.len() {
                triple_count += 1;
                if line_concurrency_determinant(lines[first], lines[second], lines[third]).is_zero()
                {
                    concurrent_triple_count += 1;
                }
            }
        }
    }

    AffineLineArrangementQuality {
        simple: parallel_pair_count == 0
            && concurrent_triple_count == 0
            && infinity_degenerate_line_count == 0,
        pair_count,
        triple_count,
        parallel_pair_count,
        concurrent_triple_count,
        infinity_degenerate_line_count,
    }
}

pub fn homogenize_affine_bivariate_to_p3<const P: i64>(
    polynomial: &AffinePlanePolynomialFp<P>,
    degree: usize,
    x_var: usize,
    y_var: usize,
    w_var: usize,
) -> PolynomialP3Fp<P> {
    assert!(x_var < P3_VARIABLE_COUNT);
    assert!(y_var < P3_VARIABLE_COUNT);
    assert!(w_var < P3_VARIABLE_COUNT);
    assert!(x_var != y_var && x_var != w_var && y_var != w_var);

    PolynomialP3Fp::<P>::from_terms(
        polynomial
            .terms()
            .into_iter()
            .map(|term| {
                let [x_power, y_power] = term.exponents();
                let term_degree = x_power + y_power;
                assert!(term_degree <= degree, "cannot homogenize term above degree");
                let mut exponents = [0; P3_VARIABLE_COUNT];
                exponents[x_var] = x_power;
                exponents[y_var] = y_power;
                exponents[w_var] = degree - term_degree;
                (term.coefficient(), exponents)
            })
            .collect(),
    )
}

pub fn chebyshev_t8_homogeneous<const P: i64>(
    variable: &PolynomialP3Fp<P>,
    homogenizer: &PolynomialP3Fp<P>,
) -> PolynomialP3Fp<P> {
    monomial_pair(variable, 8, homogenizer, 0, 128)
        .add(&monomial_pair(variable, 6, homogenizer, 2, -256))
        .add(&monomial_pair(variable, 4, homogenizer, 4, 160))
        .add(&monomial_pair(variable, 2, homogenizer, 6, -32))
        .add(&monomial_pair(variable, 0, homogenizer, 8, 1))
}

pub fn chebyshev_profile_surface<const P: i64>(
    affine_polynomial: &AffinePlanePolynomialFp<P>,
    pair: WeightedCriticalPair<P>,
) -> PolynomialP3Fp<P> {
    let [_x, _y, z, w] = std::array::from_fn(PolynomialP3Fp::<P>::variable);
    let homogenized = homogenize_affine_bivariate_to_p3(affine_polynomial, 8, 0, 1, 3);
    homogenized
        .scale(pair.chebyshev_scale())
        .add(&chebyshev_t8_homogeneous(&z, &w))
        .add(&w.pow_usize(8).scale(pair.chebyshev_lambda()))
}

fn line_direction_determinant<const P: i64>(
    first: AffineLineFp<P>,
    second: AffineLineFp<P>,
) -> Fp<P> {
    first[0] * second[1] - second[0] * first[1]
}

fn line_direction_is_zero<const P: i64>(line: AffineLineFp<P>) -> bool {
    line[0].is_zero() && line[1].is_zero()
}

fn line_concurrency_determinant<const P: i64>(
    first: AffineLineFp<P>,
    second: AffineLineFp<P>,
    third: AffineLineFp<P>,
) -> Fp<P> {
    first[0] * (second[1] * third[2] - second[2] * third[1])
        - first[1] * (second[0] * third[2] - second[2] * third[0])
        + first[2] * (second[0] * third[1] - second[1] * third[0])
}

fn evaluate_affine_line<const P: i64>(line: AffineLineFp<P>, point: [Fp<P>; 2]) -> Fp<P> {
    line[0] * point[0] + line[1] * point[1] + line[2]
}

fn product_except<const P: i64>(
    values: &[Fp<P>],
    first_excluded: usize,
    second_excluded: Option<usize>,
) -> Fp<P> {
    values
        .iter()
        .enumerate()
        .filter(|(index, _)| *index != first_excluded && Some(*index) != second_excluded)
        .fold(Fp::one(), |product, (_, value)| product * *value)
}

fn symmetric_2x2_rank<const P: i64>(xx: Fp<P>, xy: Fp<P>, yy: Fp<P>) -> usize {
    if !(xx * yy - xy * xy).is_zero() {
        2
    } else if !xx.is_zero() || !xy.is_zero() || !yy.is_zero() {
        1
    } else {
        0
    }
}

fn monomial_pair<const P: i64>(
    left: &PolynomialP3Fp<P>,
    left_power: usize,
    right: &PolynomialP3Fp<P>,
    right_power: usize,
    coefficient: i64,
) -> PolynomialP3Fp<P> {
    left.pow_usize(left_power)
        .mul(&right.pow_usize(right_power))
        .scale(Fp::new(coefficient))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn quadratic_profile_has_one_morse_critical_point() {
        let [x, y] = std::array::from_fn(AffinePlanePolynomialFp::<31>::variable);
        let polynomial = x.pow_usize(2).add(&y.pow_usize(2));
        let profile = critical_value_profile(&polynomial);

        assert_eq!(profile.total_critical(), 1);
        assert_eq!(profile.morse_critical(), 1);
        assert_eq!(profile.degenerate_critical(), 0);
        assert_eq!(profile.bucket(Fp::new(0)).unwrap().morse_count(), 1);
    }

    #[test]
    fn cubic_profile_tracks_degenerate_critical_point() {
        let [x, y] = std::array::from_fn(AffinePlanePolynomialFp::<31>::variable);
        let polynomial = x.pow_usize(3).add(&y.pow_usize(3));
        let profile = critical_value_profile(&polynomial);

        assert_eq!(profile.total_critical(), 1);
        assert_eq!(profile.morse_critical(), 0);
        assert_eq!(profile.degenerate_critical(), 1);
        assert_eq!(profile.bucket(Fp::new(0)).unwrap().degenerate_count(), 1);
    }

    #[test]
    fn simple_eight_line_product_has_twenty_eight_zero_level_nodes() {
        let lines = slope_polynomial_lines::<31>(&[1]);
        let quality = affine_line_arrangement_quality(&lines);
        assert!(quality.simple());
        assert_eq!(quality.parallel_pair_count(), 0);
        assert_eq!(quality.concurrent_triple_count(), 0);
        assert_eq!(quality.infinity_degenerate_line_count(), 0);

        let product = line_product_polynomial(&lines);
        let profile = critical_value_profile(&product);

        assert_eq!(profile.bucket(Fp::new(0)).unwrap().morse_count(), 28);
    }

    #[test]
    fn fast_line_product_profile_matches_sparse_profile() {
        let lines = slope_polynomial_lines::<31>(&[1]);
        let product = line_product_polynomial(&lines);
        let sparse_profile = critical_value_profile(&product);
        let fast_profile = critical_value_profile_for_lines_fast(&lines);

        assert_eq!(fast_profile, sparse_profile);
    }

    #[test]
    fn normal_form10_builds_ten_parameter_eight_line_chart() {
        let arrangement =
            AffineLineArrangementFp::<31>::normal_form10([2, 3, 4, 5, 7, 1, 2, 3, 4, 5]);
        assert_eq!(arrangement.lines().len(), 8);
        assert_eq!(arrangement.lines()[0], [Fp::one(), Fp::zero(), Fp::zero()]);
        assert_eq!(arrangement.lines()[1], [Fp::zero(), Fp::one(), Fp::zero()]);
        assert_eq!(arrangement.lines()[2], [-Fp::one(), -Fp::one(), Fp::one()]);
        assert_eq!(arrangement.lines()[3], [Fp::new(2), Fp::one(), Fp::one()]);
        assert!(arrangement.quality().simple());
    }

    #[test]
    fn arrangement_quality_detects_parallel_triple_and_infinity_degeneracy() {
        let parallel = vec![
            [Fp::<31>::one(), Fp::zero(), Fp::zero()],
            [Fp::one(), Fp::zero(), Fp::one()],
        ];
        assert_eq!(
            affine_line_arrangement_quality(&parallel).parallel_pair_count(),
            1
        );

        let triple = vec![
            [Fp::<31>::one(), Fp::zero(), Fp::zero()],
            [Fp::zero(), Fp::one(), Fp::zero()],
            [Fp::one(), Fp::one(), Fp::zero()],
        ];
        assert_eq!(
            affine_line_arrangement_quality(&triple).concurrent_triple_count(),
            1
        );

        let infinity_degenerate = vec![[Fp::<31>::zero(), Fp::zero(), Fp::one()]];
        assert_eq!(
            affine_line_arrangement_quality(&infinity_degenerate).infinity_degenerate_line_count(),
            1
        );
        assert!(!affine_line_arrangement_quality(&infinity_degenerate).simple());
    }

    #[test]
    fn homogenization_preserves_affine_evaluation_at_w_one() {
        let [x, y] = std::array::from_fn(AffinePlanePolynomialFp::<31>::variable);
        let polynomial = x
            .pow_usize(3)
            .add(&x.mul(&y).scale(Fp::new(5)))
            .add(&AffinePlanePolynomialFp::<31>::constant(Fp::new(7)));
        let homogenized = homogenize_affine_bivariate_to_p3(&polynomial, 8, 0, 1, 3);

        assert!(homogenized.is_homogeneous());
        assert_eq!(homogenized.degree(), 8);

        let affine_point = [Fp::new(2), Fp::new(3)];
        let projective_point = [Fp::new(2), Fp::new(3), Fp::new(0), Fp::one()];
        assert_eq!(
            polynomial.evaluate(&affine_point),
            homogenized.evaluate(&projective_point)
        );
    }
}
