const crateList = document.getElementById('crate-list');
Object.entries(crates).forEach(([crateName, _crateMetadata]) => {
    let code = document.createElement('code');
    code.appendChild(document.createTextNode(crateName));
    let a = document.createElement('a');
    a.appendChild(code);
    a.setAttribute("href", `${crateName}/index.html`);
    let li = document.createElement('li');
    li.appendChild(a);
    crateList.appendChild(li);
});


