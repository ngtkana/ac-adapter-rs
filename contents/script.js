document.addEventListener('DOMContentLoaded', function () {
  const app = document.getElementById("app");
  const sidebar = document.getElementById("catalog-list");
  const searchInput = document.getElementById("search-input");
  const main = document.getElementById("catalog-main");

  // 検索インデックスの読み込み（型・関数名でもクレートを見つけられるようにする）
  let itemsByCrate = {};

  function loadSearchIndex() {
    const script = document.createElement('script');
    script.src = 'rustdoc/search-index.js';
    script.onload = function () {
      if (typeof window.searchIndex !== 'undefined') {
        processSearchIndex(window.searchIndex);
      }
    };
    document.head.appendChild(script);
  }

  function processSearchIndex(searchIndex) {
    searchIndex.forEach((crateData, crateName) => {
      if (!itemsByCrate[crateName]) {
        itemsByCrate[crateName] = [];
      }
      if (crateData.n && Array.isArray(crateData.n)) {
        crateData.n.forEach((itemName, index) => {
          const doc = (crateData.d && crateData.d[index]) || '';
          itemsByCrate[crateName].push({ name: itemName, doc });
        });
      }
    });
  }

  function renderMath(el) {
    if (window.renderMathInElement) {
      renderMathInElement(el, {
        delimiters: [
          { left: "$$", right: "$$", display: true },
          { left: "$", right: "$", display: false },
        ],
      });
    }
  }

  // "tag:xxx" トークンとそれ以外の全文検索トークンに分割
  function parseQuery(raw) {
    const tokens = raw.trim().toLowerCase().split(/\s+/).filter(Boolean);
    const tagQueries = [];
    const textQueries = [];
    tokens.forEach(t => {
      const m = t.match(/^tag:(.+)$/);
      if (m) tagQueries.push(m[1]); else textQueries.push(t);
    });
    return { tagQueries, textQueries };
  }

  function crateMatchesText(crateName, crateMetadata, query) {
    if (crateName.toLowerCase().includes(query)) return true;
    if (crateMetadata.description && crateMetadata.description.toLowerCase().includes(query)) return true;
    const items = itemsByCrate[crateName] || [];
    return items.some(item =>
      item.name.toLowerCase().includes(query) ||
      (item.doc && item.doc.toLowerCase().includes(query)));
  }

  // std/core/alloc の既知アイテム名。intra-doc linkがこれらを指す場合はstdの公式ドキュメントへ飛ばす。
  const STD_KNOWN_IDENTS = new Set([
    'Vec', 'VecDeque', 'HashMap', 'HashSet', 'BTreeMap', 'BTreeSet', 'BinaryHeap', 'LinkedList',
    'String', 'str', 'Option', 'Result', 'Box', 'Rc', 'Arc', 'Cow', 'RefCell', 'Cell', 'Mutex',
    'RwLock', 'Ordering', 'Duration', 'Instant', 'PhantomData', 'Iterator', 'IntoIterator',
    'Default', 'Clone', 'Copy', 'Debug', 'Display', 'Hash', 'PartialEq', 'Eq', 'PartialOrd', 'Ord',
    'From', 'Into', 'TryFrom', 'TryInto', 'usize', 'isize', 'u8', 'u16', 'u32', 'u64', 'u128',
    'i8', 'i16', 'i32', 'i64', 'i128', 'f32', 'f64', 'bool', 'char',
  ]);

  // intra-doc linkの参照先テキスト（`Vec<u64>`, `std::cmp::Ordering`, `access`等）から、
  // std/core/allocのアイテムだと判定できればstd公式ドキュメントの検索結果へのURLを返す。
  function stdDocLinkFor(refText) {
    // refTextはHTMLエスケープ済み（<code>の中身）なので "<" は "&lt;" になっている
    const base = refText.split(/[<(]|&lt;/)[0].trim();
    if (/^(std|core|alloc)::/.test(base)) {
      return `https://doc.rust-lang.org/std/index.html?search=${encodeURIComponent(base.split('::').pop())}`;
    }
    const lastSegment = base.split('::').pop();
    if (STD_KNOWN_IDENTS.has(lastSegment)) {
      return `https://doc.rust-lang.org/std/index.html?search=${encodeURIComponent(lastSegment)}`;
    }
    return null;
  }

  // rustdocのintra-doc link記法（[`Item`]や[`Item`][]）をリンクにする。
  // std/core/allocのアイテムはdoc.rust-lang.orgの検索結果へ、それ以外はクレートのrustdocトップへ飛ばす。
  // 正確なアイテムのページ（struct.Foo.html等）はrustdocのsearch-indexが持つ型コードが
  // 非公開・不安定な内部フォーマットなので解読せず、確実に存在するページに留める。
  // <pre>...</pre>（コード例）の中身は対象外にする。
  function linkifyIntraDocRefs(html, crateName) {
    const localTarget = `rustdoc/${crateName}/index.html`;
    return html.split(/(<pre>[\s\S]*?<\/pre>)/).map((chunk, i) => {
      if (i % 2 === 1) return chunk;
      return chunk.replace(/\[(<code>([^<]*)<\/code>)\](\[\])?/g, (_, codeSpan, refText) => {
        const stdTarget = stdDocLinkFor(refText);
        const target = stdTarget || localTarget;
        const attrs = stdTarget ? ' target="_blank" rel="noopener"' : '';
        return `<a href="${target}"${attrs}>${codeSpan}</a>`;
      });
    }).join('');
  }

  function showDetail(crateName, crateMetadata) {
    const bodyHtml = crateMetadata.full
      ? linkifyIntraDocRefs(crateMetadata.full, crateName)
      : '<p class="placeholder">(doc comment 未整備。一覧の要約のみ)</p>';
    const summaryHtml = crateMetadata.description_html
      ? linkifyIntraDocRefs(crateMetadata.description_html, crateName)
      : '';
    main.innerHTML = `
      <button type="button" class="back-to-list">← 一覧に戻る</button>
      <h2>${crateName}</h2>
      ${summaryHtml ? `<p class="summary">${summaryHtml}</p>` : ''}
      <div class="meta-bar">
        ${crateMetadata.tags.map(t => `<span class="tag-pill clickable-tag" data-tag="${t}" role="button" tabindex="0">#${t}</span>`).join("")}
        <span>依存: ${crateMetadata.dependencies.length ? crateMetadata.dependencies.join(", ") : "なし"}</span>
        <a href="rustdoc/${crateName}/index.html">rustdocはこちら →</a>
      </div>
      <div class="doc-body">${bodyHtml}</div>
    `;
    main.querySelector(".back-to-list").addEventListener("click", () => {
      app.classList.remove("mobile-detail");
    });
    main.querySelectorAll(".clickable-tag").forEach(el => {
      const activate = () => {
        searchInput.value = `tag:${el.dataset.tag}`;
        renderList();
      };
      el.addEventListener("click", activate);
      el.addEventListener("keydown", e => {
        if (e.key === "Enter" || e.key === " ") {
          e.preventDefault();
          activate();
        }
      });
    });
    renderMath(main);
  }

  function selectItem(item) {
    document.querySelectorAll(".catalog-item").forEach(el => el.classList.remove("selected"));
    item.classList.add("selected");
    item.scrollIntoView({ block: "nearest" });
    showDetail(item.dataset.crate, dependencies[item.dataset.crate]);
    app.classList.add("mobile-detail");
  }

  function renderList() {
    const { tagQueries, textQueries } = parseQuery(searchInput.value);
    sidebar.innerHTML = '';

    Object.entries(dependencies)
      .filter(([crateName, crateMetadata]) => {
        const matchesTags = tagQueries.every(tq =>
          (crateMetadata.tags || []).some(t => t.toLowerCase().includes(tq)));
        const matchesText = textQueries.every(q => crateMatchesText(crateName, crateMetadata, q));
        return matchesTags && matchesText;
      })
      .sort(([a], [b]) => a.localeCompare(b))
      .forEach(([crateName, crateMetadata]) => {
        const item = document.createElement("div");
        item.className = "catalog-item";
        item.dataset.crate = crateName;
        item.innerHTML = `<span class="name">${crateName}</span><span class="desc">${crateMetadata.description_html || ''}</span>`;
        item.addEventListener("click", () => selectItem(item));
        sidebar.appendChild(item);
      });

    if (!sidebar.children.length) {
      sidebar.innerHTML = '<p class="placeholder">該当するライブラリが見つかりません。</p>';
    }
    renderMath(sidebar);
  }

  // j/k で前後のクレートに移動、/ で検索欄にフォーカス、Esc で検索欄を離れる
  document.addEventListener('keydown', (e) => {
    if (document.activeElement === searchInput) {
      if (e.key === 'Escape') searchInput.blur();
      return;
    }
    const items = Array.from(sidebar.querySelectorAll('.catalog-item'));
    if (!items.length) return;
    if (e.key === 'j' || e.key === 'k') {
      e.preventDefault();
      const currentIndex = items.findIndex(el => el.classList.contains('selected'));
      const step = e.key === 'j' ? 1 : -1;
      const nextIndex = Math.max(0, Math.min(items.length - 1, currentIndex + step));
      selectItem(items[nextIndex]);
    } else if (e.key === '/') {
      e.preventDefault();
      searchInput.focus();
    }
  });

  if (typeof dependencies !== 'undefined') {
    loadSearchIndex();
    renderList();
    searchInput.addEventListener('input', renderList);
    // KaTeX CDN の読み込みが遅延した場合の保険として、初回表示後にもう一度だけ再レンダリングする
    setTimeout(() => renderMath(sidebar), 1500);
  } else {
    sidebar.innerHTML = '<p class="error-text">ライブラリ情報の読み込みに失敗しました。</p>';
  }
});
