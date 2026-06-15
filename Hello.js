export default {
  async fetch(request) {
    return new Response("Hello from my Cloudflare Worker! 🚀", {
      headers: { "content-type": "text/plain" }
    });
  }
}
