use cargo_metadata::DependencyKind;
use cargo_metadata::MetadataCommand;
use std::collections::HashMap;
use std::fs;
use std::path::PathBuf;

#[derive(Clone, Debug, PartialEq, serde::Serialize)]
struct CrateMetadata {
    dependencies: Vec<String>,
    tags: Vec<String>,
    /// crate root doc comment の要約行（1行目）のプレーンテキスト。検索用。
    description: Option<String>,
    /// 要約行を HTML にレンダリングしたもの。表示用。
    description_html: Option<String>,
    /// crate root doc comment の要約行より後（本文）を HTML にレンダリングしたもの。
    full: Option<String>,
}

fn main() {
    let metadata = MetadataCommand::new().no_deps().exec().unwrap();
    let project_root = metadata.workspace_root.clone();

    let crate_metadatas: HashMap<String, CrateMetadata> = metadata
        .packages
        .iter()
        .filter(|package| package.manifest_path.starts_with(project_root.join("libs")))
        .map(|package| {
            let dependencies = package
                .dependencies
                .iter()
                .filter(|dep| dep.kind == DependencyKind::Normal && dep.path.is_some())
                .map(|dep| dep.name.clone())
                .collect();
            let tags = package.keywords.clone();
            let lib_rs_path: PathBuf = package
                .manifest_path
                .parent()
                .unwrap()
                .join("src")
                .join("lib.rs")
                .into();
            let (description, description_html, full) = fs::read_to_string(&lib_rs_path)
                .map(|content| parse_crate_docs(&content))
                .unwrap_or((None, None, None));

            (
                package.name.clone(),
                CrateMetadata {
                    dependencies,
                    tags,
                    description,
                    description_html,
                    full,
                },
            )
        })
        .collect();

    let json = serde_json::to_string(&crate_metadatas).unwrap();
    let docs_dir = PathBuf::from(&project_root).join("docs");
    fs::create_dir_all(&docs_dir).unwrap();
    fs::write(
        docs_dir.join("dependencies.js"),
        format!("dependencies = {json}"),
    )
    .unwrap();
}

/// crate ルートの `//!` doc comment を、要約行（1行目）と本文（2行目以降を HTML レンダリングしたもの）に分ける。
fn parse_crate_docs(lib_rs_content: &str) -> (Option<String>, Option<String>, Option<String>) {
    let lines: Vec<&str> = lib_rs_content
        .lines()
        .take_while(|line| line.starts_with("//!"))
        .map(|line| {
            let rest = &line["//!".len()..];
            rest.strip_prefix(' ').unwrap_or(rest)
        })
        .collect();

    let mut idx = 0;
    while idx < lines.len() && lines[idx].trim().is_empty() {
        idx += 1;
    }
    if idx >= lines.len() {
        return (None, None, None);
    }
    let description = lines[idx].trim().to_owned();
    let description_html = render_markdown(&description, true);
    idx += 1;
    while idx < lines.len() && lines[idx].trim().is_empty() {
        idx += 1;
    }
    if idx >= lines.len() {
        return (Some(description), Some(description_html), None);
    }

    let markdown = lines[idx..].join("\n");
    let full = render_markdown(&markdown, false);
    (Some(description), Some(description_html), Some(full))
}

const MARKDOWN_OPTIONS: pulldown_cmark::Options = pulldown_cmark::Options::ENABLE_TABLES;

/// Markdown を HTML にレンダリングする。`$...$` / `$$...$$` の数式は、CommonMark のバックスラッシュ
/// エスケープ規則（`\{` 等の記号直前のバックスラッシュを除去してしまう）で LaTeX が壊れないよう、
/// パース前に退避させてパース後に生の内容のまま復元する。
fn render_markdown(markdown: &str, inline_only: bool) -> String {
    let (protected, math_spans) = protect_math(markdown);
    let mut html = String::new();
    pulldown_cmark::html::push_html(
        &mut html,
        pulldown_cmark::Parser::new_ext(&protected, MARKDOWN_OPTIONS),
    );
    for (i, span) in math_spans.iter().enumerate() {
        html = html.replace(&math_placeholder(i), &escape_html_minimal(span));
    }
    if inline_only {
        html = strip_outer_block_tag(html.trim());
    }
    html
}

/// 要約行（1行目）は常にインライン表示したいが、`# 見出し`のようにMarkdownの
/// ブロック要素（`<h1>`〜`<h6>`, `<p>`, `<blockquote>`等）としてレンダリングされることがある。
/// それらのタグをそのまま埋め込むと表示先の文脈（`<p class="summary">`等）でレイアウトが壊れるため、
/// 最外周のブロックタグ1つだけを剥がしてテキストとして扱う。
fn strip_outer_block_tag(html: &str) -> String {
    if let Some(rest) = html.strip_prefix('<')
        && let Some(tag_end) = rest.find('>')
    {
        let tag_name = rest[..tag_end].split_whitespace().next().unwrap_or("");
        let closing = format!("</{tag_name}>");
        if !tag_name.is_empty() && !tag_name.starts_with('/') && html.ends_with(&closing) {
            return html[tag_end + 2..html.len() - closing.len()].to_owned();
        }
    }
    html.to_owned()
}

fn math_placeholder(index: usize) -> String {
    format!("KATEXMATHPLACEHOLDER{index}")
}

/// `$...$`（インライン）・`$$...$$`（ディスプレイ）の数式部分をプレースホルダーに置き換える。
/// `\$` はエスケープされたただのドル記号として扱い、数式の区切りとは見なさない。
fn protect_math(markdown: &str) -> (String, Vec<String>) {
    let chars: Vec<char> = markdown.chars().collect();
    let mut protected = String::with_capacity(markdown.len());
    let mut math_spans = Vec::new();
    let mut i = 0;
    while i < chars.len() {
        if chars[i] == '\\' && i + 1 < chars.len() {
            protected.push(chars[i]);
            protected.push(chars[i + 1]);
            i += 2;
            continue;
        }
        if chars[i] == '$' {
            let display = chars.get(i + 1) == Some(&'$');
            let delim_len = if display { 2 } else { 1 };
            let mut j = i + delim_len;
            let mut end = None;
            while j < chars.len() {
                if chars[j] == '\\' && j + 1 < chars.len() {
                    j += 2;
                    continue;
                }
                if !display && chars[j] == '\n' {
                    break;
                }
                if chars[j] == '$' && (!display || chars.get(j + 1) == Some(&'$')) {
                    end = Some(j + delim_len);
                    break;
                }
                j += 1;
            }
            if let Some(end) = end {
                let span: String = chars[i..end].iter().collect();
                protected.push_str(&math_placeholder(math_spans.len()));
                math_spans.push(span);
                i = end;
                continue;
            }
        }
        protected.push(chars[i]);
        i += 1;
    }
    (protected, math_spans)
}

fn escape_html_minimal(s: &str) -> String {
    s.replace('&', "&amp;")
        .replace('<', "&lt;")
        .replace('>', "&gt;")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn tables_are_rendered() {
        let markdown = "| a | b |\n|---|---|\n| 1 | 2 |\n";
        let html = render_markdown(markdown, false);
        assert!(html.contains("<table>"), "got: {html}");
    }

    #[test]
    fn latex_punctuation_escapes_survive_markdown() {
        // `\{`, `\}`, `\,`, `\#` はいずれも CommonMark 的には「記号の前のバックスラッシュ除去」
        // の対象だが、数式中では KaTeX コマンドとしてバックスラッシュを残す必要がある。
        let markdown = r"$\# \{\, x \,\}$";
        let html = render_markdown(markdown, false);
        assert!(html.contains(r"$\# \{\, x \,\}$"), "got: {html}");
    }

    #[test]
    fn angle_brackets_in_math_are_html_escaped() {
        let markdown = "$a < b$";
        let html = render_markdown(markdown, false);
        assert!(html.contains("$a &lt; b$"), "got: {html}");
    }

    #[test]
    fn heading_as_description_is_unwrapped_to_plain_text() {
        let (_, description_html, _) = parse_crate_docs("//! # Manacher's algorithm\n");
        assert_eq!(description_html.unwrap(), "Manacher's algorithm");
    }

    #[test]
    fn description_is_rendered_as_inline_html_without_p_wrapper() {
        let (_, description_html, _) =
            parse_crate_docs("//! [`Vec<u64>`] の話 $O(n)$\n//!\n//! 本文。\n");
        let html = description_html.unwrap();
        assert!(!html.contains("<p>"), "got: {html}");
        assert!(html.contains("<code>Vec&lt;u64&gt;</code>"), "got: {html}");
        assert!(html.contains("$O(n)$"), "got: {html}");
    }
}
