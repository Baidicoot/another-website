const config = require("./config");
const templates = require("./templates");
const fs = require("fs");
const fm = require("front-matter");
const md = require("./remarked-config");

const format = ([dir,page]) => {
    const data = fs.readFileSync(`${config.indir}${dir.join("")}${page}.md`, "utf8")
    const content = fm(data)
    content.body = md.md.render(content.body)
    content.path = [dir,page]
    content.root = "../".repeat(dir.length)
    return content
};

const formatSource = ([dir,page,ext]) => {
    const data = fs.readFileSync(`${config.indir}${dir.join("")}${page}.${ext}`, "utf8")
    const lang = config.extensions[ext]
    return {
        body: md.hljs.highlight(lang, data).value,
        src: data,
        path: [dir,`${page}.${ext}`],
        root: "../".repeat(dir.length)
    }
}

const recMkDir = (root,dir) => {
    if (dir.length > 0) {
        if (!fs.existsSync(`${root}${dir[0]}`)) {
            fs.mkdirSync(`${root}${dir[0]}`)
        }
        recMkDir(root+dir[0],dir.slice(1))
    }
}

const handle = post => e => {
    if (e) throw e
    console.log(`${post.path[0].join("")}${post.path[1]}.html was created successfully`)
}

const generate = posts => {
    posts.forEach(post => {
        recMkDir(config.outdir,post.path[0])
        
        fs.writeFile(
            `${config.outdir}${post.path[0].join("")}${post.path[1]}.html`,
            templates.page(post),
            handle(post))
    })
}

const generateSource = sourcefiles => {
    sourcefiles.forEach(post => {
        recMkDir(config.outdir,post.path[0])

        fs.writeFile(
            `${config.outdir}${post.path[0].join("")}${post.path[1]}.html`,
            templates.source(post),
            handle(post))
        fs.writeFile(
            `${config.outdir}${post.path[0].join("")}${post.path[1]}`,
            post.src,
            e => {if (e) throw e})
    })
}

module.exports = {
    format: format,
    generate: generate,
    formatSrc: formatSource,
    generateSrc: generateSource
};