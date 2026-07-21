(() => {
  const isWeChatMiniGame = typeof wx !== "undefined" && typeof wx.getStorageSync === "function";
  const hasBrowserStorage = typeof localStorage !== "undefined";

  const storage = {
    get(key) {
      try {
        return isWeChatMiniGame ? wx.getStorageSync(key) || "" : hasBrowserStorage ? localStorage.getItem(key) || "" : "";
      } catch {
        return "";
      }
    },
    set(key, value) {
      try {
        if (isWeChatMiniGame) wx.setStorageSync(key, value);
        else if (hasBrowserStorage) localStorage.setItem(key, value);
      } catch {
        // Storage is optional; gameplay continues when a host blocks persistence.
      }
    }
  };

  const frame = typeof requestAnimationFrame === "function"
    ? requestAnimationFrame.bind(globalThis)
    : callback => setTimeout(() => callback(Date.now()), 16);

  globalThis.GamePlatform = Object.freeze({
    target: isWeChatMiniGame ? "wechat-minigame" : "web",
    storage,
    frame,
    delay: (callback, ms) => setTimeout(callback, ms)
  });
})();
