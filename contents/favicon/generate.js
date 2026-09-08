// Regenerates ../favicon.svg and ../favicon-{16,32}x{16,32}.png / ../apple-touch-icon.png
//   npm install
//   node generate.js
const { chromium } = require("playwright");
const fs = require("fs");
const path = require("path");

const SRC = path.resolve(__dirname, "favicon.svg");
const OUT_DIR = path.resolve(__dirname, "..");
const SIZES = [
  { file: "favicon-16x16.png", size: 16 },
  { file: "favicon-32x32.png", size: 32 },
  { file: "apple-touch-icon.png", size: 180 },
];

(async () => {
  fs.copyFileSync(SRC, path.join(OUT_DIR, "favicon.svg"));

  const svg = fs.readFileSync(SRC, "utf8");
  const browser = await chromium.launch();
  for (const { file, size } of SIZES) {
    const page = await browser.newPage({ viewport: { width: size, height: size } });
    await page.setContent(
      `<!DOCTYPE html><html><head><style>html,body{margin:0;padding:0;}svg{display:block;}</style></head><body>${svg}</body></html>`,
    );
    await page.evaluate((s) => {
      const el = document.querySelector("svg");
      el.setAttribute("width", s);
      el.setAttribute("height", s);
    }, size);
    await page.screenshot({ path: path.join(OUT_DIR, file) });
    await page.close();
  }
  await browser.close();
})();
