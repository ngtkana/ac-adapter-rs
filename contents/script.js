document.addEventListener('DOMContentLoaded', function () {
  const crateList = document.getElementById("crate-list");
  const searchInput = document.getElementById("search-input");
  const viewGrid = document.getElementById("view-grid");
  const viewList = document.getElementById("view-list");

  // クレートリストの生成
  function renderCrateList(filter = '') {
    crateList.innerHTML = '';

    Object.entries(dependencies).forEach(([crateName, crateMetadata]) => {
      // 名前でフィルタリング
      if (filter && !crateName.toLowerCase().includes(filter.toLowerCase())) {
        return;
      }

      // クレートカードの作成
      const col = document.createElement("div");
      col.className = viewGrid.classList.contains('active') ? 'col-md-4 mb-4' : 'col-12 mb-3';

      const card = document.createElement("div");
      card.className = "card crate-card";

      const cardBody = document.createElement("div");
      cardBody.className = "card-body";

      // クレート名とリンク
      const title = document.createElement("h5");
      title.className = "card-title";

      const link = document.createElement("a");
      link.href = `rustdoc/${crateName}/index.html`;

      // 検索ハイライト
      if (filter && crateName.toLowerCase().includes(filter.toLowerCase())) {
        const regex = new RegExp(`(${filter})`, 'gi');
        link.innerHTML = crateName.replace(regex, '<span class="highlight">$1</span>');
      } else {
        link.textContent = crateName;
      }

      title.appendChild(link);
      cardBody.appendChild(title);

      // 説明文（あれば）
      if (crateMetadata.description) {
        const desc = document.createElement("p");
        desc.className = "card-text";
        desc.textContent = crateMetadata.description;
        cardBody.appendChild(desc);
      }

      // 依存関係
      if (crateMetadata.dependencies && crateMetadata.dependencies.length > 0) {
        const deps = document.createElement("p");
        deps.className = "card-text small text-muted";
        deps.innerHTML = `<strong>依存:</strong> ${crateMetadata.dependencies.map(dep =>
          `<a href="rustdoc/${dep}/index.html">${dep}</a>`).join(', ')}`;
        cardBody.appendChild(deps);
      }

      card.appendChild(cardBody);
      col.appendChild(card);
      crateList.appendChild(col);
    });

    // 結果がない場合のメッセージ
    if (crateList.children.length === 0) {
      const noResults = document.createElement("div");
      noResults.className = "col-12 text-center py-5";
      noResults.innerHTML = `<p class="text-muted">検索条件に一致するライブラリが見つかりませんでした。</p>`;
      crateList.appendChild(noResults);
    }
  }

  // 初期化
  if (typeof dependencies !== 'undefined') {
    renderCrateList();

    // 検索機能
    searchInput.addEventListener('input', function () {
      renderCrateList(this.value);
    });

    // 表示切り替え
    viewGrid.addEventListener('click', function () {
      viewList.classList.remove('active');
      viewGrid.classList.add('active');
      document.querySelectorAll('#crate-list > div').forEach(el => {
        if (!el.classList.contains('text-center')) { // 「結果がない」メッセージは除外
          el.className = 'col-md-4 mb-4';
        }
      });
    });

    viewList.addEventListener('click', function () {
      viewGrid.classList.remove('active');
      viewList.classList.add('active');
      document.querySelectorAll('#crate-list > div').forEach(el => {
        if (!el.classList.contains('text-center')) { // 「結果がない」メッセージは除外
          el.className = 'col-12 mb-3';
        }
      });
    });
  } else {
    // dependencies.js が読み込まれていない場合
    crateList.innerHTML = '<div class="col-12 text-center py-5"><p class="text-danger">ライブラリ情報の読み込みに失敗しました。</p></div>';
  }
});
