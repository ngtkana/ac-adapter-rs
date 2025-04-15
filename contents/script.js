document.addEventListener('DOMContentLoaded', function () {
  const crateList = document.getElementById("crate-list");
  const searchInput = document.getElementById("search-input");
  const viewGrid = document.getElementById("view-grid");
  const viewList = document.getElementById("view-list");

  // 検索インデックスの読み込み
  let searchIndex = null;
  let itemsByCrate = {};

  // search-index.js を読み込む
  function loadSearchIndex() {
    const script = document.createElement('script');
    script.src = 'rustdoc/search-index.js';
    script.onload = function () {
      if (typeof searchIndex !== 'undefined') {
        processSearchIndex();
      }
    };
    document.head.appendChild(script);
  }

  // 検索インデックスを処理して、クレートごとのアイテムのマップを作成
  function processSearchIndex() {
    if (!window.searchIndex) return;

    searchIndex = window.searchIndex;

    // クレートごとにアイテムをマッピング
    searchIndex.forEach((crateData, crateName) => {
      if (!itemsByCrate[crateName]) {
        itemsByCrate[crateName] = [];
      }

      // アイテム名の配列を取得
      if (crateData.n && Array.isArray(crateData.n)) {
        crateData.n.forEach((itemName, index) => {
          // ドキュメントがあれば取得
          let doc = '';
          if (crateData.d && Array.isArray(crateData.d) && crateData.d[index]) {
            doc = crateData.d[index];
          }

          itemsByCrate[crateName].push({
            name: itemName,
            doc: doc,
            index: index
          });
        });
      }
    });
  }

  // クレートリストの生成
  function renderCrateList(filter = '') {
    crateList.innerHTML = '';

    // 検索結果を格納する配列
    const matchedCrates = [];
    const matchedItems = {};

    Object.entries(dependencies).forEach(([crateName, crateMetadata]) => {
      let crateMatches = false;
      let matchingItems = [];

      // クレート名でフィルタリング
      if (!filter || crateName.toLowerCase().includes(filter.toLowerCase())) {
        crateMatches = true;
      }

      // アイテムでフィルタリング
      if (filter && itemsByCrate[crateName]) {
        itemsByCrate[crateName].forEach(item => {
          if (
            item.name.toLowerCase().includes(filter.toLowerCase()) ||
            (item.doc && item.doc.toLowerCase().includes(filter.toLowerCase()))
          ) {
            matchingItems.push(item);
            crateMatches = true;
          }
        });
      }

      if (crateMatches) {
        matchedCrates.push(crateName);
        if (matchingItems.length > 0) {
          matchedItems[crateName] = matchingItems;
        }
      }
    });

    // 検索結果を表示
    matchedCrates.forEach(crateName => {
      const crateMetadata = dependencies[crateName];

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
        const regex = new RegExp(`(${filter.replace(/[.*+?^${}()|[\]\\]/g, '\\$&')})`, 'gi');
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

      // マッチしたアイテムを表示
      if (matchedItems[crateName] && matchedItems[crateName].length > 0) {
        const matchedItemsDiv = document.createElement("div");
        matchedItemsDiv.className = "matched-items mt-2";

        const matchedItemsTitle = document.createElement("p");
        matchedItemsTitle.className = "mb-1 fw-bold";
        matchedItemsTitle.textContent = "マッチしたアイテム:";
        matchedItemsDiv.appendChild(matchedItemsTitle);

        const matchedItemsList = document.createElement("ul");
        matchedItemsList.className = "list-unstyled ms-2 small";

        // 最大5つまで表示
        const itemsToShow = matchedItems[crateName].slice(0, 5);
        itemsToShow.forEach(item => {
          const itemLi = document.createElement("li");

          const itemLink = document.createElement("a");
          itemLink.href = `rustdoc/${crateName}/index.html#${item.name}`;

          // 検索ハイライト
          if (filter && item.name.toLowerCase().includes(filter.toLowerCase())) {
            const regex = new RegExp(`(${filter.replace(/[.*+?^${}()|[\]\\]/g, '\\$&')})`, 'gi');
            itemLink.innerHTML = item.name.replace(regex, '<span class="highlight">$1</span>');
          } else {
            itemLink.textContent = item.name;
          }

          itemLi.appendChild(itemLink);

          // ドキュメントがあれば表示
          if (item.doc) {
            const docSpan = document.createElement("span");
            docSpan.className = "text-muted ms-2";

            // ドキュメントを短く切り詰める
            let shortDoc = item.doc;
            if (shortDoc.length > 50) {
              shortDoc = shortDoc.substring(0, 50) + "...";
            }

            // 検索ハイライト
            if (filter && shortDoc.toLowerCase().includes(filter.toLowerCase())) {
              const regex = new RegExp(`(${filter.replace(/[.*+?^${}()|[\]\\]/g, '\\$&')})`, 'gi');
              docSpan.innerHTML = shortDoc.replace(regex, '<span class="highlight">$1</span>');
            } else {
              docSpan.textContent = shortDoc;
            }

            itemLi.appendChild(docSpan);
          }

          matchedItemsList.appendChild(itemLi);
        });

        // 表示しきれないアイテムがある場合
        if (matchedItems[crateName].length > 5) {
          const moreLi = document.createElement("li");
          moreLi.className = "text-muted";
          moreLi.textContent = `他 ${matchedItems[crateName].length - 5} アイテム...`;
          matchedItemsList.appendChild(moreLi);
        }

        matchedItemsDiv.appendChild(matchedItemsList);
        cardBody.appendChild(matchedItemsDiv);
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
    // 検索インデックスを読み込む
    loadSearchIndex();

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
