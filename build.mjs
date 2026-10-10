import * as esbuild from 'esbuild';
import fs from 'node:fs';

// One source, two outputs:
//   dist/index.html       the page body for the Claude-hosted copy (the host adds the document skeleton)
//   dist/site/index.html  a complete standalone page for GitHub Pages
// dist/preview.html wraps the first for local browser checks.
const TITLE = 'COMPX361 Test 2 Trainer';
const DESCRIPTION = 'Step-by-step practice for COMPX361 Test 2: Turing numbers, grammars, propositional and predicate logic, induction.';

const prod = !process.argv.includes('--dev');
async function bundle(define = {}) {
  const r = await esbuild.build({
    entryPoints: ['src/ui/main.jsx'],
    bundle: true,
    minify: prod,
    format: 'iife',
    write: false,
    jsx: 'automatic',
    jsxImportSource: 'preact',
    target: ['es2020'],
    loader: { '.js': 'jsx' },
    legalComments: 'none',
    logLevel: 'warning',
    define,
  });
  return r.outputFiles[0].text.replace(/<\/script/gi, '<\\/script')
    // esbuild keeps control characters raw inside strings; escape them so the page is plain text
    .replace(/[\x00-\x08\x0b\x0c\x0e-\x1f]/g, (c) => '\\u' + c.charCodeAt(0).toString(16).padStart(4, '0'));
}

const css = fs.readFileSync('src/ui/styles.css', 'utf8');
const fonts = 'https://fonts.googleapis.com/css2?family=Atkinson+Hyperlegible+Next:ital,wght@0,200..800;1,200..800&family=Martian+Mono:wdth,wght@75..112.5,100..800&family=STIX+Two+Text:ital,wght@0,400..700;1,400..700&family=Noto+Sans+Math&display=swap';
const fontLinks = `<link rel="preconnect" href="https://fonts.googleapis.com">
<link rel="preconnect" href="https://fonts.gstatic.com" crossorigin>
<link rel="stylesheet" href="${fonts}">`;
// Set the theme before the first paint: Light unless the viewer has chosen Dark or System.
const themeBoot = `<script>var t='light';try{var p=JSON.parse(localStorage.getItem('compx361-t2-trainer-v1')||'{}').prefs;if(p&&(p.theme==='dark'||p.theme==='system'))t=p.theme}catch(e){}if(t!=='system')document.documentElement.setAttribute('data-user-theme',t)</script>`;

// ---- Claude-hosted copy
const page = `<title>${TITLE}</title>
${themeBoot}
<meta name="description" content="${DESCRIPTION}">
${fontLinks}
<style>${css}</style>
<div id="app"></div>
<script>${await bundle()}</script>
`;
fs.mkdirSync('dist/site', { recursive: true });
fs.writeFileSync('dist/index.html', page);
const localFonts = fs.existsSync('tools/preview-fonts.css') ? `<style>${fs.readFileSync('tools/preview-fonts.css', 'utf8')}</style>` : '';
fs.writeFileSync('dist/preview.html', `<!doctype html><html><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1,viewport-fit=cover"><style>:root{color-scheme:light}body{margin:0;font-family:system-ui,sans-serif;font-size:14px}img{max-width:100%}[hidden]{display:none!important}</style>${localFonts}</head><body>${page.replace(/<link rel="stylesheet"[^>]+>/, '')}</body></html>`);

// ---- GitHub Pages copy: a whole document. It can't use Claude marking, so it doesn't mention it.
// Icon: a strip of the course's punched tape ("1", "4", "/").
const holes = ['10001', '10100', '11111'].flatMap((code, c) => [...code].map((b, r) => (b === '1'
  ? `<circle cx="${9 + c * 7}" cy="${6 + r * 5}" r="2.2" fill="#fbfcfe"/>`
  : `<circle cx="${9 + c * 7}" cy="${6 + r * 5}" r="1.6" fill="none" stroke="#5f6b86" stroke-width="0.9"/>`)));
const icon = 'data:image/svg+xml,' + encodeURIComponent(`<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 32 32"><rect width="32" height="32" rx="7" fill="#141e36"/>${holes.join('')}</svg>`);
const site = `<!doctype html>
<html lang="en-NZ">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<title>${TITLE}</title>
<meta name="description" content="${DESCRIPTION}">
<meta name="robots" content="noindex">
<meta property="og:type" content="website">
<meta property="og:title" content="${TITLE}">
<meta property="og:description" content="${DESCRIPTION}">
<link rel="icon" href="${icon}">
${themeBoot}
${fontLinks}
<style>body{margin:0}img{max-width:100%}[hidden]{display:none!important}</style>
<style>${css}</style>
</head>
<body>
<noscript><p style="padding:24px;font-family:system-ui,sans-serif">The trainer needs JavaScript switched on.</p></noscript>
<div id="app"></div>
<script>${await bundle({ __STANDALONE__: 'true' })}</script>
</body>
</html>
`;
fs.writeFileSync('dist/site/index.html', site);
console.log(`built: ${(page.length / 1024).toFixed(0)} KB for Claude, ${(site.length / 1024).toFixed(0)} KB for GitHub Pages`);
