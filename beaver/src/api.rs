use argh::FromArgs;
use serde::Deserialize;
use crate::index::IndexReader;

#[derive(Debug, Deserialize)]
pub struct Machine {
    pub machine_code: String,
    pub machine_id: u32,
    pub status: Status,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum Status {
    Decided,
    Undecided,
}

#[derive(Debug, Deserialize)]
struct DeciderResult {
    decider_file: String,
}

pub fn get_decider(index: u32) -> Option<String> {
    let url = format!("https://api.bbchallenge.org/machine/{index}");
    let response = ureq::get(&url)
        .call().unwrap()
        .into_string().unwrap();

    let machine: Machine = serde_json::from_str(&response).unwrap();

    if machine.status == Status::Undecided {
        return None;
    }

    let url = format!("https://api.bbchallenge.org/machine/{index}/decider");
    let response = ureq::get(&url)
        .call().unwrap()
        .into_string().unwrap();

    let response: DeciderResult = serde_json::from_str(&response).unwrap();

    Some(response.decider_file)
}

#[derive(FromArgs)]
#[argh(subcommand, name = "query")]
/// query the status of the specified machines
pub struct Query {
    /// machines to query (index or index file)
    #[argh(positional)]
    indices: Vec<String>,
}

impl Query {
    pub fn run(&self) {
        let show = |index| {
            let decider = get_decider(index);
            let decider = decider.as_ref()
                .map(|s| s.as_str())
                .unwrap_or("UNDECIDED");
            println!("{index:8} {decider}");
        };

        for input in &self.indices {
            if let Ok(v) = input.parse() {
                show(v);
            } else {
                let file = IndexReader::open(input).unwrap();
                for index in file {
                    show(index);
                }
            }
        }
    }
}
