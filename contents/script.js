document.addEventListener('DOMContentLoaded', function () {
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

  function showDetail(crateName, crateMetadata) {
    const bodyHtml = crateMetadata.full
      ? crateMetadata.full
      : '<p class="placeholder">(doc comment 未整備。一覧の要約のみ)</p>';
    main.innerHTML = `
      <h4>${crateName}</h4>
      ${crateMetadata.description ? `<p class="summary">${crateMetadata.description}</p>` : ''}
      <div class="meta-bar">
        ${crateMetadata.tags.map(t => `<span class="tag-pill clickable-tag" data-tag="${t}">#${t}</span>`).join("")}
        <span>依存: ${crateMetadata.dependencies.length ? crateMetadata.dependencies.join(", ") : "なし"}</span>
        <a href="rustdoc/${crateName}/index.html">rustdocはこちら →</a>
      </div>
      <div class="doc-body">${bodyHtml}</div>
    `;
    main.querySelectorAll(".clickable-tag").forEach(el => {
      el.addEventListener("click", () => {
        searchInput.value = `tag:${el.dataset.tag}`;
        renderList();
      });
    });
    renderMath(main);
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
        item.innerHTML = `<span class="name">${crateName}</span><span class="desc">${crateMetadata.description || ''}</span>`;
        item.addEventListener("click", () => {
          document.querySelectorAll(".catalog-item").forEach(el => el.classList.remove("selected"));
          item.classList.add("selected");
          showDetail(crateName, crateMetadata);
        });
        sidebar.appendChild(item);
      });

    if (!sidebar.children.length) {
      sidebar.innerHTML = '<p class="placeholder">該当するライブラリが見つかりません。</p>';
    }
    renderMath(sidebar);
  }

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
