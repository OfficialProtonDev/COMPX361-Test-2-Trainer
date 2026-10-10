// Which copy this is. The GitHub Pages build defines __STANDALONE__: Claude marking can't run there,
// so that copy doesn't mention it at all. The Claude-hosted copy offers it when the viewer allows.
/* global __STANDALONE__ */
export const STANDALONE = typeof __STANDALONE__ !== 'undefined' && __STANDALONE__ === true;
