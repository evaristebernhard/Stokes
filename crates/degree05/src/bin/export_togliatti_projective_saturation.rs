use degree05::togliatti_quintic;
use nodal_core::{P3_VARIABLE_COUNT, Rational, SparsePolynomial};

type PolynomialP3 = SparsePolynomial<Rational, P3_VARIABLE_COUNT>;

fn main() {
    let variables = ["x0", "x1", "x2", "x3"];
    let surface = togliatti_quintic();
    let polynomial = surface.polynomial();

    println!("// Generated from crates/degree05 Catanese Proposition 130 determinant model.");
    println!("// Projective Jacobian ideal J=<F,Fx0,Fx1,Fx2,Fx3>, saturated by <x0,x1,x2,x3>.");
    println!("LIB \"elim.lib\";");
    println!("ring r = 0,({}),dp;", variables.join(","));
    print_certificate_proc();
    println!(
        "poly F = {};",
        singular_polynomial(&polynomial.to_sparse(), &variables)
    );
    for variable in 0..P3_VARIABLE_COUNT {
        println!(
            "poly d{} = {};",
            variable,
            singular_polynomial(
                &polynomial.partial_derivative(variable).to_sparse(),
                &variables
            )
        );
    }
    println!("ideal J = F,d0,d1,d2,d3;");
    println!("ideal irrelevant = x0,x1,x2,x3;");
    println!("ideal saturatedJ = sat(J, irrelevant);");
    println!("ideal G = std(saturatedJ);");
    println!("print(\"# projective_jacobian_saturation\");");
    println!("print(\"# singular_order dp\");");
    println!("print(\"# saturated_basis_size \"+string(size(G)));");
    println!("degree(G);");
    println!("print(\"order grevlex\");");
    println!("print(\"\");");
    println!("print(\"generators\");");
    println!("printCertificatePoly(F);");
    println!("printCertificatePoly(d0);");
    println!("printCertificatePoly(d1);");
    println!("printCertificatePoly(d2);");
    println!("printCertificatePoly(d3);");
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

fn singular_polynomial(polynomial: &PolynomialP3, variables: &[&str; 4]) -> String {
    let terms = polynomial.terms();
    if terms.is_empty() {
        return "0".to_string();
    }

    terms
        .iter()
        .map(|term| {
            let coefficient = term.coefficient();
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
