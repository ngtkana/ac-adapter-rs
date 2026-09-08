// Regenerates ../logo.png from cover.html.
//   npm install
//   node generate.js
const { chromium } = require("playwright");
const path = require("path");

(async () => {
  const browser = await chromium.launch();
  const page = await browser.newPage({ viewport: { width: 1200, height: 630 } });
  await page.goto("file://" + path.resolve(__dirname, "cover.html"));
  await page.waitForTimeout(300); // let the web font finish loading
  await page.screenshot({ path: path.resolve(__dirname, "..", "logo.png") });
  await browser.close();
})();
