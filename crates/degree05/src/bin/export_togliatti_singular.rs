use degree05::{togliatti_affine_chart_generators, togliatti_affine_chart_variable_indices};
use nodal_core::{AFFINE_P3_VARIABLE_COUNT, Rational, SparsePolynomial};
use std::env;
use std::fmt;
use std::process;

type PolynomialA3 = SparsePolynomial<Rational, AFFINE_P3_VARIABLE_COUNT>;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum ExportOrder {
    Lex,
    GrevLex,
}

impl ExportOrder {
    fn singular_name(self) -> &'static str {
        match self {
            Self::Lex => "lp",
            Self::GrevLex => "dp",
        }
    }

    fn certificate_name(self) -> &'static str {
        match self {
            Self::Lex => "lex",
            Self::GrevLex => "grevlex",
        }
    }
}

impl fmt::Display for ExportOrder {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.certificate_name())
    }
}

fn main() {
    let args: Vec<_> = env::args().collect();
    let (chart_variable, order) = match parse_args(&args) {
        Ok(config) => config,
        Err(message) => {
            eprintln!("{message}");
            eprintln!("usage: export_togliatti_singular <chart 0..3> [lex|grevlex]");
            process::exit(2);
        }
    };

    let generators = togliatti_affine_chart_generators(chart_variable);
    let variables = ["u0", "u1", "u2"];
    let projective_indices = togliatti_affine_chart_variable_indices(chart_variable);

    println!("// Generated from crates/degree05 Catanese Proposition 130 determinant model.");
    println!(
        "// Chart x{} = 1; affine variables ({}, {}, {}) correspond to projective variables ({}, {}, {}).",
        chart_variable,
        variables[0],
        variables[1],
        variables[2],
        projective_indices[0],
        projective_indices[1],
        projective_indices[2]
    );
    println!(
        "ring r = 0,({}),{};",
        variables.join(","),
        order.singular_name()
    );
    println!("option(redSB);");
    print_certificate_proc();
    for (index, generator) in generators.iter().enumerate() {
        println!(
            "poly f{} = {};",
            index + 1,
            singular_polynomial(generator, &variables)
        );
    }
    println!("ideal I = f1,f2,f3,f4;");
    println!("ideal G = std(I);");
    println!("print(\"# chart_variable {}\");", chart_variable);
    println!(
        "print(\"# affine_projective_indices {} {} {}\");",
        projective_indices[0], projective_indices[1], projective_indices[2]
    );
    println!("print(\"# singular_order {}\");", order.singular_name());
    println!("print(\"# basis_size \"+string(size(G)));");
    println!("print(\"# vdim \"+string(vdim(G)));");
    println!("print(\"order {}\");", order.certificate_name());
    println!("print(\"\");");
    println!("print(\"generators\");");
    println!("printCertificatePoly(f1);");
    println!("printCertificatePoly(f2);");
    println!("printCertificatePoly(f3);");
    println!("printCertificatePoly(f4);");
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

fn parse_args(args: &[String]) -> Result<(usize, ExportOrder), String> {
    if args.len() < 2 || args.len() > 3 {
        return Err("expected chart variable and optional order".to_string());
    }

    let chart_variable = args[1]
        .parse::<usize>()
        .map_err(|error| format!("invalid chart variable `{}`: {error}", args[1]))?;
    if chart_variable >= 4 {
        return Err("chart variable must be between 0 and 3".to_string());
    }

    let order = if let Some(order) = args.get(2) {
        match order.to_ascii_lowercase().as_str() {
            "lex" => ExportOrder::Lex,
            "grevlex" => ExportOrder::GrevLex,
            _ => return Err(format!("unsupported order `{order}`; use lex or grevlex")),
        }
    } else {
        ExportOrder::GrevLex
    };

    Ok((chart_variable, order))
}

fn singular_polynomial(polynomial: &PolynomialA3, variables: &[&str; 3]) -> String {
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
