const fs = require("fs");
const config = require("./config");
const format = require("./format");

const treepages = (root,dir) => fs
  .readdirSync(root+dir.join(""))
  .map(page => fs.lstatSync(root+dir.join("")+page).isDirectory() ? treepages(root,[...dir,page+"/"]) : [[dir,page]])
  .reduce((a,b) => [...a,...b], [])

const pages = treepages(config.indir,[])
  .map(([dir,page]) => [dir,page.slice(0, -3)])
  .map(page => format.format(page))

if (!fs.existsSync(config.outdir)) fs.mkdirSync(config.outdir);

format.generate(pages);