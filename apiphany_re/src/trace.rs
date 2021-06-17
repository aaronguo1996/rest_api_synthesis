use har::{
    from_reader,
    v1_2::{Entries, Log},
    Har, Spec,
};
use lasso::Spur;
use regex::RegexSet;
use serde_json::Value;
use soa_derive::StructOfArray;

/// A `Method` is an API method.
#[derive(Debug, Copy, Clone)]
pub enum Method {
    Get,
    Post,
    Unsupported,
}

// TODO: try using smallvec for this and manually do the soa transform later on
/// An input parameter in a trace entry.
/// Since input parameters normally come in lists, we also do the soa transform
/// on this struct too.
#[derive(Debug, StructOfArray)]
#[soa_derive = "Debug"]
pub struct Param {
    pub arg_name: Spur,
    pub value: Value,
    pub required: bool,
}

/// A `Trace` is a trace entry.
/// We store these Traces in a struct-of-arrays fashion since normally,
/// we only care about one of the fields of each trace.
#[derive(Debug, StructOfArray)]
#[soa_derive = "Debug"]
pub struct Trace {
    pub endpoint: Spur,
    pub method: Method,
    pub params: ParamVec,
    // option to account for error responses
    pub response: Option<Value>,
}

/// A `TraceParser` is a simplified version of the trace entry parser in
/// `analyzer/parser.py`. It's reimplemented here since it's ultimately easier
/// to parse the log ourselves than try to marshal to/from Python for the trace
/// entries (they're already on disk!)
pub struct TraceParser {
    log_file: String,
    hostname: String,
    path_to_defs: String,
    endpoints: String,
    base_path: String,
}

impl TraceParser {
    pub fn new(
        log_file: String,
        hostname: String,
        path_to_defs: String,
        endpoints: String,
        base_path: String,
    ) -> Self {
        Self {
            log_file,
            hostname,
            path_to_defs,
            endpoints,
            base_path,
        }
    }

    /// Parse a bunch of trace entries!
    pub fn parse_entries(&self, skips: &[String], skip_fields: &[String]) -> TraceVec {
        let mut res = TraceVec::new();
        let file = std::fs::File::open(&self.log_file)
            .ok()
            .expect("couldn't open log file");
        let reader = std::io::BufReader::new(file);

        let log: Log = match from_reader(reader).expect("couldn't read har from log").log {
            Spec::V1_2(l) => l,
            _ => panic!("har 1.3 unsupported"),
        };

        for e in &log.entries {
            let url = &e.request.url;
            let skip_set = RegexSet::new(skips).unwrap();
            if skip_set.is_match(url) {
                continue;
            }

            // Only try resolving the entry if it's json and the hostname is right
            if e.response.content.mime_type == "application/json" && url.contains(&self.hostname) {
                if let Some(e) = self.resolve_entry(e, skip_fields) {
                    res.push(e);
                }
            }
        }

        res
    }

    fn resolve_entry(&self, entry: &Entries, skip_fields: &[String]) -> Option<Trace> {
        let request = &entry.request;
        // todo: get endpoint
        let method = match request.method.as_str() {
            "GET" => Method::Get,
            "POST" => Method::Post,
            _ => return None,
        };

        // resolve parameters

        // resolve response

        todo!()
    }
}
