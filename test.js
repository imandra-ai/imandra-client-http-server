console.log('system working');

let url = "http://localhost:3000/decompose/by-src/instances";

function dosubmit (e) {
    e.preventDefault();

    let contents = "fun (x : example) -> " + document.getElementById('program').value;

    let req = JSON.stringify({ src_base64: btoa(contents), syntax: "iml" });

    fetch(url, { method: 'POST', body: req }).then(function (res) {
        res.json().then(function (json) {
            console.log(json);
            let str = JSON.stringify(json);
            console.log(str);
            let output = document.getElementById('output');
            console.log(output);
            output.innerHTML = str;
        });
    });

    return false;
}

document.getElementById('form').addEventListener('submit', dosubmit);
