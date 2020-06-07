const config = require("./config");
const templates = require("./templates");
const fs = require("fs");
const fm = require("front-matter");
const marked = require("./marked-config");

const format = path => {
    const data = fs.readFileSync(`${config.indir}/${path}.md`, "utf8");
    const content = fm(data);
    content.body = marked(content.body);
    content.path = path;
    return content;
};

const generate = posts => {
    posts.forEach(post => {
        if (!fs.existsSync(`${config.outdir}/${post.path}`)) {
            fs.mkdirSync(`${config.outdir}/${post.path}`);
        }

        fs.writeFile(
            `${config.outdir}/${post.path}/index.html`,
            templates.page(post),
            e => {
                if (e) throw e;
                console.log(`${post.path}/index.html was created successfully`);
            });
    });
};

module.exports = {
    format: format,
    generate: generate
};