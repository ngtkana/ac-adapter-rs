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
        const attrs = stdTarget ? ' target="_blank" rel="noopener noreferrer"' : '';
        const newTabNote = stdTarget ? '<span class="visually-hidden">（新しいタブで開く）</span>' : '';
        return `<a href="${target}"${attrs}>${codeSpan}${newTabNote}</a>`;
      });
    }).join('');
  }

  // crate doc の見出し（h1〜）を2段下げる。ページの h1（サイト名）→ h2（クレート名）の下に来るようにする。
  function demoteHeadings(html) {
    return html.replace(/<(\/?)h([1-6])(?=[\s>])/g, (_, slash, level) =>
      `<${slash}h${Math.min(6, Number(level) + 2)}`);
  }

  function showDetail(crateName, crateMetadata) {
    const bodyHtml = crateMetadata.full
      ? demoteHeadings(linkifyIntraDocRefs(crateMetadata.full, crateName))
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
        <a href="rustdoc/${crateName}/index.html">${crateName} の rustdoc →</a>
      </div>
      <div class="doc-body">${bodyHtml}</div>
    `;
    main.querySelector(".back-to-list").addEventListener("click", () => {
      history.back();
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

  // 一覧⇔詳細の1画面切り替えはモバイル幅（styles.cssの768pxブレークポイントと同一基準）専用の挙動。
  // デスクトップでは常に両方表示されるため、履歴やフォーカスを操作しない。
  function isMobileLayout() {
    return window.matchMedia("(max-width: 768px)").matches;
  }

  function showMobileDetailView() {
    app.classList.add("mobile-detail");
    main.focus();
  }

  function hideMobileDetailView() {
    app.classList.remove("mobile-detail");
    (sidebar.querySelector(".catalog-item.selected") || sidebar).focus();
  }

  // モバイルの一覧⇔詳細切り替えをブラウザの戻る/進む操作（スワイプ等）に対応させる。
  // 複数クレートを見た後でも「戻る」は常に一覧へ一直線に戻したいので、
  // 既に詳細状態のhistory entryがあれば積み増さずreplaceする。
  function enterDetail() {
    if (!isMobileLayout()) return;
    if (history.state && history.state.view === "detail") {
      history.replaceState({ view: "detail" }, "");
    } else {
      history.pushState({ view: "detail" }, "");
    }
    showMobileDetailView();
  }

  window.addEventListener("popstate", (e) => {
    if (!isMobileLayout()) return;
    if (e.state && e.state.view === "detail") showMobileDetailView();
    else hideMobileDetailView();
  });

  // 詳細表示中のクレート名。一覧の再描画（検索・タグ絞り込み）後も選択状態を復元するために保持する
  let selectedCrate = null;

  function selectItem(item) {
    selectedCrate = item.dataset.crate;
    const focusWasInList = sidebar.contains(document.activeElement);
    document.querySelectorAll(".catalog-item").forEach(el => {
      el.classList.remove("selected");
      el.removeAttribute("aria-current");
      el.tabIndex = -1;
    });
    item.classList.add("selected");
    item.setAttribute("aria-current", "true");
    item.tabIndex = 0;
    // j/k でリスト内を移動したときはフォーカスも追従させる
    if (focusWasInList) item.focus({ preventScroll: true });
    item.scrollIntoView({ block: "nearest" });
    showDetail(item.dataset.crate, dependencies[item.dataset.crate]);
    enterDetail();
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
        const item = document.createElement("button");
        item.type = "button";
        item.className = "catalog-item";
        item.dataset.crate = crateName;
        if (crateName === selectedCrate) {
          item.classList.add("selected");
          item.setAttribute("aria-current", "true");
        }
        item.innerHTML = `<span class="name">${crateName}</span><span class="desc">${crateMetadata.description_html || ''}</span>`;
        // roving tabindex: 一覧全体を Tab ストップ1つにし、項目間は j/k・↑/↓ で移動する
        item.tabIndex = crateName === selectedCrate ? 0 : -1;
        item.addEventListener("click", () => selectItem(item));
        sidebar.appendChild(item);
      });

    // 選択中の項目が絞り込みで消えた（または未選択の）場合は先頭を Tab ストップにする
    if (!sidebar.querySelector('.catalog-item[tabindex="0"]')) {
      const first = sidebar.querySelector(".catalog-item");
      if (first) first.tabIndex = 0;
    }

    if (!sidebar.children.length) {
      sidebar.innerHTML = '<p class="placeholder">該当するライブラリが見つかりません。</p>';
    }
    renderMath(sidebar);
  }

  // j/k（一覧にフォーカスがあるときは ↑/↓ も）で前後のクレートに移動、/ で検索欄にフォーカス、Esc で検索欄を離れる
  document.addEventListener('keydown', (e) => {
    if (document.activeElement === searchInput) {
      if (e.key === 'Escape') searchInput.blur();
      return;
    }
    const items = Array.from(sidebar.querySelectorAll('.catalog-item'));
    if (!items.length) return;
    const arrowInList = (e.key === 'ArrowDown' || e.key === 'ArrowUp') && sidebar.contains(document.activeElement);
    if (e.key === 'j' || e.key === 'k' || arrowInList) {
      e.preventDefault();
      const currentIndex = items.findIndex(el => el.classList.contains('selected'));
      const step = (e.key === 'j' || e.key === 'ArrowDown') ? 1 : -1;
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
