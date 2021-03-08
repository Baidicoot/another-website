const fs = require("fs")
const template = require('es6-template-strings');

const pagestr = fs.readFileSync("templates/main.html", "utf8");
const sourcestr = fs.readFileSync("templates/source.html", "utf8");

const page = data => {
    return template(pagestr, {data:data});
}

const source = data => {
    return template(sourcestr, {data:data});
}

module.exports = {
    page: page,
    source: source
};