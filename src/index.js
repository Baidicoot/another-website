const fs = require("fs");
const config = require("./config");
const format = require("./format");

const treepages = (root,dir) => fs
  .readdirSync(root+dir.join(""))
  .map(page => fs.lstatSync(root+dir.join("")+page).isDirectory() ? treepages(root,[...dir,page+"/"]) : [[dir,page]])
  .reduce((a,b) => [...a,...b], [])

const files = treepages(config.indir,[])

const pages = files
  .filter(([dir,page]) => page.slice(-3) === ".md")
  .map(([dir,page]) => [dir,page.slice(0, -3)])
  .map(format.format)

const sourcefiles = files
  .map(([dir,page]) => [dir,page.slice(0,page.lastIndexOf('.')),page.slice(page.lastIndexOf('.')+1)])
  .filter(([dir,page,ext]) => ext in config.extensions)
  .map(format.formatSrc)

if (!fs.existsSync(config.outdir)) fs.mkdirSync(config.outdir);

format.generate(pages);
format.generateSrc(sourcefiles);