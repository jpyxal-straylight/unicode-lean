// Cross-port differential runner — C++ side.
//
// Reads /tmp/diff_corpus.jsonl (shared with rust-port and python-port),
// runs homoglyph_confusable::detect on each entry, and emits one JSONL
// line to stdout in the canonical cross-port format:
//
//   {"id":<n>,"cps":[<u32>,…],"kind":"<Clear|Hazard>","sub":"<tag|null>","target":"<str|null>"}
//
// Any byte-level divergence from the rust-port / python-port output of
// this same corpus is a port-drift bug.
//
// Build:
//   g++ -std=c++23 -O2 -Iinclude -o build/diff_runner tools/diff_runner.cpp
// Run:
//   build/diff_runner > /tmp/cpp_diff.jsonl

#include <cstdint>
#include <fstream>
#include <iostream>
#include <span>
#include <sstream>
#include <string>
#include <variant>
#include <vector>

#include "unicode_cpp/security/identity/homoglyph_confusable.hpp"

namespace h = unicode_cpp::security::homoglyph_confusable;
using unicode_cpp::security::ClassificationKind;

namespace {

constexpr const char* CORPUS_PATH = "/tmp/diff_corpus.jsonl";

// Minimal hand parser of `{"id":N,"cps":[a,b,c]}`.  Mirrors the
// rust-port parser exactly so the corpus protocol matches.
bool parse_corpus_line(
    const std::string& line, std::size_t& id_out,
    std::vector<std::uint32_t>& cps_out) {
    cps_out.clear();
    const std::size_t id_field = line.find("\"id\":");
    if (id_field == std::string::npos) return false;
    const std::size_t id_start = id_field + 5;
    const std::size_t id_end = line.find(',', id_start);
    if (id_end == std::string::npos) return false;
    id_out = static_cast<std::size_t>(
        std::stoull(line.substr(id_start, id_end - id_start)));
    const std::size_t arr_field = line.find("\"cps\":[");
    if (arr_field == std::string::npos) return false;
    const std::size_t arr_start = arr_field + 7;
    const std::size_t arr_end = line.find(']', arr_start);
    if (arr_end == std::string::npos) return false;
    std::string body = line.substr(arr_start, arr_end - arr_start);
    if (body.empty()) return true;
    std::size_t tok_start = 0;
    for (std::size_t i = 0; i <= body.size(); ++i) {
        if (i == body.size() || body[i] == ',') {
            if (i > tok_start) {
                cps_out.push_back(static_cast<std::uint32_t>(
                    std::stoul(body.substr(tok_start, i - tok_start))));
            }
            tok_start = i + 1;
        }
    }
    return true;
}

std::string escape_json(const std::string& s) {
    std::string out;
    out.reserve(s.size() + 4);
    for (char c : s) {
        if (c == '"') out += "\\\"";
        else out += c;
    }
    return out;
}

std::string verdict_to_jsonl(
    std::size_t id, const std::vector<std::uint32_t>& cps,
    const h::Database& db) {
    auto v = h::detect(std::span<const std::uint32_t>(cps), db);
    const char* kind = nullptr;
    switch (v.kind) {
        case ClassificationKind::Clear:         kind = "Clear"; break;
        case ClassificationKind::Hazard:        kind = "Hazard"; break;
        case ClassificationKind::Compound:      kind = "Compound"; break;
        case ClassificationKind::Informational: kind = "Informational"; break;
    }
    std::string sub_str = "null";
    std::string target_str = "null";
    if (v.sub.has_value()) {
        const std::string tag = h::sub_threat_tag(*v.sub);
        sub_str = "\"" + tag + "\"";
        if (std::holds_alternative<h::TargetMatch>(*v.sub)) {
            const auto& tm = std::get<h::TargetMatch>(*v.sub);
            target_str = "\"" + escape_json(tm.target) + "\"";
        }
    }
    std::ostringstream oss;
    oss << "{\"id\":" << id << ",\"cps\":[";
    for (std::size_t i = 0; i < cps.size(); ++i) {
        if (i > 0) oss << ',';
        oss << cps[i];
    }
    oss << "],\"kind\":\"" << kind << "\","
        << "\"sub\":" << sub_str << ","
        << "\"target\":" << target_str << "}";
    return oss.str();
}

}  // namespace

int main() {
    const auto db = h::Database::load_from_dir("data");
    std::ifstream f(CORPUS_PATH);
    if (!f) {
        std::cerr << "FATAL: cannot open " << CORPUS_PATH
                  << " — run the rust-port diff_gen_corpus first\n";
        return 1;
    }
    std::string line;
    while (std::getline(f, line)) {
        if (line.empty()) continue;
        std::size_t id = 0;
        std::vector<std::uint32_t> cps;
        if (!parse_corpus_line(line, id, cps)) {
            std::cerr << "FATAL: malformed corpus line: " << line << '\n';
            return 1;
        }
        std::cout << verdict_to_jsonl(id, cps, db) << '\n';
    }
    return 0;
}
