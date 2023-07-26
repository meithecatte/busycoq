mod database;
mod turing;
use database::Database;

fn main() {
    let mut db = Database::open("../seed.dat").unwrap();
    let n = db.num_total as usize;
    for tm in db.iter().skip(n - 5).take(10) {
        println!("{tm}");
    }
}
