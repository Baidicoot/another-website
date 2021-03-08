const remarkable = require('remarkable');
const katex = require('remarkable-katex');
const hljs = require("highlight.js");

const rpncc = (hljs) => {
  return {
    case_insensitive: false,
    keywords: {
      keyword:'export import include library',
    },
    contains: [
      {
        className: 'string',
        begin: '`', end: '`'
      },
      hljs.COMMENT(
        /^#/,
        /$/,
      ),
      {
        className: 'symbol',
        begin: /(;|\(#|#\)|\(|\))/,
      },
      {
        className: 'function',
        begin: '->',
      },
      {
        className: 'builtin',
        begin: '\'',
      },
      {
        className: 'number',
        begin: /[0-9]+/
      },
      {
        className: 'meta',
        begin: /\(#/,
        end: /#\)/,
        contains: [{
          className: 'keyword',
          begin: /(import|include|library)/,
        }]
      }
    ]
  }
}

const att = (hljs) => {
  return {
    case_insensitive: false,
    keywords: {
      keyword: 'Axiom Definition Compute Check Unfolding Print Reduction Constraint Universes All',
      built_in: 'forall fun Type'
    },
    contains: [
      hljs.COMMENT('\\(\\*', '\\*\\)'),
      {
        className: 'symbol',
        begin: /:=|\.|[-=]>/
      }
    ]
  }
}

hljs.registerLanguage("rpncc", rpncc);
hljs.registerLanguage("att", att);

var md = new remarkable.Remarkable({
  html: true,
  highlight: function (str, lang) {
    if (lang && hljs.getLanguage(lang)) {
      try {
        return hljs.highlight(lang, str).value;
      } catch (err) {}
    }
    try {
      return hljs.highlightAuto(str).value;
    } catch (err) {}
    return '';
  }
});

md.use(katex)

module.exports = {md: md, hljs: hljs};