const fs = require("fs");
const config = require("./config");
const format = require("./format");

const pages = fs
  .readdirSync(config.indir)
  .map(page => page.slice(0, -3))
  .map(page => format.format(page));

if (!fs.existsSync(config.outdir)) fs.mkdirSync(config.outdir);

format.generate(pages);