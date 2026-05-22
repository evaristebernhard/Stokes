use degree05::{
    TOGLIATTI_PROJECTIVE_STRATUM_VARIABLE_COUNT,
    special_togliatti_infinity_support_stratum_generators,
};
use nodal_core::{QuadraticRational, Rational, SparsePolynomial};
use std::env;
use std::process;

type PolynomialA4 =
    SparsePolynomial<QuadraticRational, TOGLIATTI_PROJECTIVE_STRATUM_VARIABLE_COUNT>;

fn main() {
    let args: Vec<_> = env::args().collect();
    let support_mask = match parse_args(&args) {
        Ok(mask) => mask,
        Err(message) => {
            eprintln!("{message}");
            eprintln!(
                "usage: export_special_togliatti_projective_strata <infinity-support-mask 1..7>"
            );
            process::exit(2);
        }
    };

    let stratum = special_togliatti_infinity_support_stratum_generators(support_mask);
    let variables = ["u0", "u1", "u2", "tau"];
    let affine_indices = stratum.affine_projective_indices();

    println!("// Generated from the Catanese 2.5.1 special Togliatti quintic model.");
    println!(
        "// Infinity support mask {support_mask}; chart x{} = 1.",
        stratum.chart_variable()
    );
    println!("ring r = (0,t),({}),dp;", variables.join(","));
    println!("minpoly = t^2-5;");
    println!("option(redSB);");
    print_certificate_proc();
    for (index, generator) in stratum.generators().iter().enumerate() {
        println!(
            "poly f{} = {};",
            index + 1,
            singular_polynomial(generator, &variables)
        );
    }
    let generator_names = (1..=stratum.generators().len())
        .map(|index| format!("f{index}"))
        .collect::<Vec<_>>()
        .join(",");
    println!("ideal I = {generator_names};");
    println!("ideal G = std(I);");
    println!("print(\"# special_togliatti_infinity_support_mask {support_mask}\");");
    println!("print(\"# chart_variable {}\");", stratum.chart_variable());
    println!(
        "print(\"# affine_projective_indices {} {} {}\");",
        affine_indices[0], affine_indices[1], affine_indices[2]
    );
    println!("print(\"# coefficient_field Qsqrt5\");");
    println!("print(\"# singular_order dp\");");
    println!("print(\"# basis_size \"+string(size(G)));");
    println!("print(\"# vdim \"+string(vdim(G)));");
    println!("print(\"order grevlex\");");
    println!("print(\"\");");
    println!("print(\"generators\");");
    for index in 1..=stratum.generators().len() {
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

fn parse_args(args: &[String]) -> Result<u8, String> {
    if args.len() != 2 {
        return Err("expected infinity support mask".to_string());
    }

    let support_mask = args[1]
        .parse::<u8>()
        .map_err(|error| format!("invalid support mask `{}`: {error}", args[1]))?;
    if !(1..=7).contains(&support_mask) {
        return Err("infinity support mask must be between 1 and 7".to_string());
    }

    Ok(support_mask)
}

fn singular_polynomial(polynomial: &PolynomialA4, variables: &[&str; 4]) -> String {
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

    parts.join("+").replace("+-", "-")
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
