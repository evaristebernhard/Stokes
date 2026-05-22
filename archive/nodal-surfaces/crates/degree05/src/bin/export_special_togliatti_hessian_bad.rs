use degree05::special_togliatti_affine_chart3_hessian_degenerate_generators;
use nodal_core::{AFFINE_P3_VARIABLE_COUNT, QuadraticRational, Rational, SparsePolynomial};

type PolynomialA3 = SparsePolynomial<QuadraticRational, AFFINE_P3_VARIABLE_COUNT>;

fn main() {
    let generators = special_togliatti_affine_chart3_hessian_degenerate_generators();
    let variables = ["u0", "u1", "u2"];

    println!("// Generated from the Catanese 2.5.1 special Togliatti quintic model.");
    println!(
        "// Chart x3 = 1; affine variables (u0, u1, u2) correspond to projective variables (0, 1, 2)."
    );
    println!("// The fifth generator is det Hessian(F|x3=1).");
    println!("ring r = (0,t),(u0,u1,u2),dp;");
    println!("minpoly = t^2-5;");
    println!("option(redSB);");
    print_certificate_proc();
    for (index, generator) in generators.iter().enumerate() {
        println!(
            "poly f{} = {};",
            index + 1,
            singular_polynomial(generator, &variables)
        );
    }
    println!("ideal I = f1,f2,f3,f4,f5;");
    println!("ideal G = std(I);");
    println!("print(\"# special_togliatti_chart3_hessian_bad\");");
    println!("print(\"# affine_projective_indices 0 1 2\");");
    println!("print(\"# coefficient_field Qsqrt5\");");
    println!("print(\"# singular_order dp\");");
    println!("print(\"# basis_size \"+string(size(G)));");
    println!("print(\"# vdim \"+string(vdim(G)));");
    println!("print(\"order grevlex\");");
    println!("print(\"\");");
    println!("print(\"generators\");");
    for index in 1..=5 {
        println!("printCertificatePoly(f{index});");
    }
    println!("print(\"\");");
    println!("print(\"basis\");");
    println!("for (int i = 1; i <= size(G); i = i + 1) {{");
    println!("  printCertificatePoly(G[i]);");
    println!("}}");
    println!("quit;");
}

fn print_certificate_proc() {
    println!("proc printCertificatePoly(poly p)");
    println!("{{");
    println!("  print(\"poly\");");
    println!("  number c;");
    println!("  intvec e;");
    println!("  string line;");
    println!("  int i;");
    println!("  while (p != 0)");
    println!("  {{");
    println!("    c = leadcoef(p);");
    println!("    e = leadexp(p);");
    println!("    line = string(c);");
    println!("    for (i = 1; i <= nvars(basering); i = i + 1)");
    println!("    {{");
    println!("      line = line + \" \" + string(e[i]);");
    println!("    }}");
    println!("    print(line);");
    println!("    p = p - lead(p);");
    println!("  }}");
    println!("  print(\"end\");");
    println!("}}");
    println!();
}

fn singular_polynomial(polynomial: &PolynomialA3, variables: &[&str; 3]) -> String {
    let terms = polynomial.terms();
    if terms.is_empty() {
        return "0".to_string();
    }

    terms
        .iter()
        .map(|term| {
            let coefficient = singular_quadratic_rational(term.coefficient());
            let monomial = term
                .exponents()
                .iter()
                .enumerate()
                .filter_map(|(index, &exponent)| match exponent {
                    0 => None,
                    1 => Some(variables[index].to_string()),
                    _ => Some(format!("{}^{}", variables[index], exponent)),
                })
                .collect::<Vec<_>>();

            if monomial.is_empty() {
                format!("({coefficient})")
            } else {
                format!("({coefficient})*{}", monomial.join("*"))
            }
        })
        .collect::<Vec<_>>()
        .join(" + ")
}

fn singular_quadratic_rational(value: QuadraticRational) -> String {
    let rational = value.rational();
    let irrational = value.irrational();
    if irrational.is_zero() {
        return rational.to_string();
    }

    let mut parts = Vec::new();
    if !irrational.is_zero() {
        parts.push(format_rational_t(irrational));
    }
    if !rational.is_zero() {
        parts.push(rational.to_string());
    }

    parts.join("+").replace("+-", "-").replace("+ -", "-")
}

fn format_rational_t(value: Rational) -> String {
    if value == Rational::ONE {
        "t".to_string()
    } else if value == -Rational::ONE {
        "-t".to_string()
    } else {
        format!("{value}t")
    }
}
