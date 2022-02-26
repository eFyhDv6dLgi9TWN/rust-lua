extern crate pkg_config;

fn main() {
    pkg_config::Config::new()
        .probe("luajit")
        .expect("pkg-config luajit failed");
}
