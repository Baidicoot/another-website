const marked = require("marked");

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
        begin: '[0-9]+'
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

marked.setOptions({
  renderer: new marked.Renderer(),
  highlight: function(code, language) {
    const hljs = require("highlight.js");
    hljs.registerLanguage("rpncc", rpncc);
    const validLanguage = hljs.getLanguage(language) ? language : "plaintext";
    return hljs.highlight(validLanguage, code).value;
  },
  pedantic: false,
  gfm: true,
  breaks: false,
  sanitize: false,
  smartLists: true,
  smartypants: false,
  xhtml: false
});

module.exports = marked;