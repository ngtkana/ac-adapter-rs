const crateList = document.getElementById('crate-list');
crates.forEach(crate => {
    console.log(crate.name);
    let code = document.createElement('code');
    code.appendChild(document.createTextNode(crate.name));
    let a = document.createElement('a');
    a.appendChild(code);
    a.setAttribute("href", `${crate.name}/index.html`);
    let li = document.createElement('li');
    li.appendChild(a);
    crateList.appendChild(li);
});


