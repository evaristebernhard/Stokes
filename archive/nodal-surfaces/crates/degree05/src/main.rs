fn main() {
    let surface = degree05::togliatti_quintic();

    println!("Togliatti quintic over Q");
    println!("degree = {}", surface.polynomial().degree());
    println!("terms = {}", surface.polynomial().terms().len());
    println!(
        "literature node count = {}",
        degree05::togliatti_literature_node_count()
    );
    println!(
        "Beauville maximum mu(5) = {}",
        degree05::beauville_maximum_node_count()
    );
    let special_certificate = degree05::special_togliatti_singular_scheme_certificate()
        .expect("embedded special Togliatti certificates parse");
    println!(
        "special model verified projective singular length = {:?}",
        special_certificate.verified_projective_length()
    );
    println!(
        "special model verified reduced ordinary node count = {:?}",
        special_certificate.verified_reduced_ordinary_node_count()
    );
}
