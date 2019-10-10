console.log('system working');

let baseUrl = "http://localhost:3000";
let submit = document.getElementById('submit');

function dosubmit (e) {
    e.preventDefault();

    let contents = document.getElementById('program').value;

    let req = JSON.stringify({ src_base64: btoa(contents), syntax: "iml" });

    submit.disabled = true;
    fetch(baseUrl + '/reset', { method: 'POST'}).then(function () {
        return fetch(baseUrl + '/decompose/by-src/instances', { method: 'POST', body: req }).then(function (res) {
            res.json().then(function (json) {
                let str = JSON.stringify(json);
                let output = document.getElementById('output');
                output.innerHTML = str;

                submit.disabled = false;
            });
        });
    });

    return false;
}

document.getElementById('form').addEventListener('submit', dosubmit);
