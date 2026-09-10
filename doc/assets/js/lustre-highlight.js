// Client-side syntax highlighting for ```lustre code blocks.
//
// Hugo's highlighter (Chroma) has no Lustre lexer and cannot load a custom one,
// so the render hook for `lustre` emits plain text and this script tokenizes it
// in the browser. The emitted markup and class names mirror Chroma's exactly
// (div.highlight > pre.chroma > code, span.line > span.cl, Pygments token
// abbreviations), so the theme's existing light/dark styles apply unchanged.

(function () {
  "use strict";

  // Keyword surface taken from src/lustre/lustreLexer.mll.
  var KEYWORDS = new Set([
    "activate", "any", "assert", "assume", "assumption_vars", "at", "auto",
    "check", "choose", "con", "cond", "condact", "const", "contract",
    "datatype", "decreases", "default", "else", "elsif", "end", "ensure",
    "every", "exists", "fby", "fi", "forall", "frame", "from", "function",
    "guarantee", "if", "import", "imported", "include", "initial", "invariant",
    "last", "lemma", "let", "match", "merge", "mode", "noc", "node", "of",
    "opaque", "otherwise", "param", "pre", "provided", "reachable", "rec",
    "require", "restart", "returns", "tel", "then", "transparent", "type",
    "var", "weakly", "when", "with", "within"
  ]);

  var TYPES = new Set([
    "array", "bool", "enum", "history", "int", "int8", "int16", "int32",
    "int64", "map", "real", "set", "sint", "struct", "subrange", "subtype",
    "uint", "uint8", "uint16", "uint32", "uint64"
  ]);

  var WORD_OPERATORS = new Set([
    "and", "div", "in", "lsh", "mod", "not", "or", "rsh", "xor"
  ]);

  var BOOLEANS = new Set(["true", "false"]);

  // Alternatives are ordered: contract delimiters before block comments (a
  // contract block holds real code, not comment text), annotations before line
  // comments, floats before integers.
  var TOKEN = new RegExp([
    "(?<contract>\\(\\*@contract|/\\*@contract|\\*\\)|\\*/)",
    "(?<annotation>--[%!]\\w*)",
    "(?<lineComment>--[^\\n]*)",
    "(?<blockComment>\\(\\*[\\s\\S]*?\\*\\)|/\\*[\\s\\S]*?\\*/)",
    "(?<string>\"[^\"\\n]*\")",
    "(?<float>\\d+\\.\\d*(?:[eE][+-]?\\d+)?|\\.\\d+(?:[eE][+-]?\\d+)?)",
    "(?<hex>0[xX][0-9a-fA-F]+)",
    "(?<int>\\d+)",
    "(?<ident>[A-Za-z_]\\w*)",
    "(?<operator>->|==>|<>|<=|>=|=>|::|:=|[-+*/^=<>|@])",
    "(?<rest>[\\s\\S])"
  ].join("|"), "gy");

  // A name is a call or declaration if the next non-space token opens an
  // argument list, optionally preceded by type arguments (`f<<int>>(x)`).
  var CALL_AHEAD = /^\s*(?:<<[^>\n]*>>)?\s*\(/;

  function escapeHtml(text) {
    return text
      .replace(/&/g, "&amp;")
      .replace(/</g, "&lt;")
      .replace(/>/g, "&gt;");
  }

  function classifyIdentifier(name, source, index) {
    if (BOOLEANS.has(name)) return "kc";
    if (WORD_OPERATORS.has(name)) return "ow";
    if (TYPES.has(name)) return "kt";
    if (KEYWORDS.has(name)) return "k";
    if (CALL_AHEAD.test(source.slice(index))) return "nf";
    return null;
  }

  function tokenize(source) {
    var tokens = [];
    TOKEN.lastIndex = 0;
    var match;
    while ((match = TOKEN.exec(source)) !== null) {
      var groups = match.groups;
      var text = match[0];
      var cls = null;
      if (groups.contract !== undefined) cls = "cm";
      else if (groups.annotation !== undefined) cls = "nd";
      else if (groups.lineComment !== undefined) cls = "c1";
      else if (groups.blockComment !== undefined) cls = "cm";
      else if (groups.string !== undefined) cls = "s";
      else if (groups.float !== undefined) cls = "mf";
      else if (groups.hex !== undefined) cls = "mh";
      else if (groups.int !== undefined) cls = "mi";
      else if (groups.operator !== undefined) cls = "o";
      else if (groups.ident !== undefined) {
        cls = classifyIdentifier(text, source, TOKEN.lastIndex);
      }
      tokens.push([cls, text]);
    }
    return tokens;
  }

  // Rebuild Chroma's line structure: a token may straddle a newline (block
  // comments do), so each line closes and reopens its own spans.
  function render(source) {
    var lines = [""];
    tokenize(source).forEach(function (token) {
      var cls = token[0];
      token[1].split("\n").forEach(function (part, i) {
        if (i > 0) lines.push("");
        if (!part) return;
        var escaped = escapeHtml(part);
        lines[lines.length - 1] +=
          cls ? '<span class="' + cls + '">' + escaped + "</span>" : escaped;
      });
    });
    return lines
      .map(function (line, i) {
        var newline = i < lines.length - 1 ? "\n" : "";
        return '<span class="line"><span class="cl">' + line + newline +
          "</span></span>";
      })
      .join("");
  }

  function highlightAll() {
    document.querySelectorAll("code.language-lustre").forEach(function (block) {
      if (block.dataset.highlighted === "true") return;
      block.innerHTML = render(block.textContent);
      block.dataset.highlighted = "true";
    });
  }

  if (document.readyState === "loading") {
    document.addEventListener("DOMContentLoaded", highlightAll);
  } else {
    highlightAll();
  }
})();
