const config = require("./config");
const templates = require("./templates");
const fs = require("fs");
const fm = require("front-matter");
const marked = require("./marked-config");

const format = ([dir,page]) => {
    const data = fs.readFileSync(`${config.indir}${dir.join("")}${page}.md`, "utf8")
    const content = fm(data)
    content.body = marked(content.body)
    content.path = [dir,page]
    content.root = "../".repeat(dir.length+1)
    return content
};

const recMkDir = (root,dir) => {
    if (dir.length > 0) {
        if (!fs.existsSync(`${root}${dir[0]}`)) {
            fs.mkdirSync(`${root}${dir[0]}`)
        }
        recMkDir(root+dir[0],dir.slice(1))
    }
}

const generate = posts => {
    posts.forEach(post => {
        recMkDir(config.outdir,[...post.path[0],post.path[1]])
        
        fs.writeFile(
            `${config.outdir}${post.path[0].join("")}${post.path[1]}/index.html`,
            templates.page(post),
            e => {
                if (e) throw e
                console.log(`${post.path[0].join("")}${post.path[1]}/index.html was created successfully`)
            })
    })
}

module.exports = {
    format: format,
    generate: generate
};