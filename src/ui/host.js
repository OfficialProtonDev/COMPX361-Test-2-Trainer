// Where this copy runs. The GitHub Pages build sets __CLAUDE_URL__ to the Claude-hosted copy, so
// pages there can point people to it for Claude marking; the Claude-hosted build leaves it empty.
/* global __CLAUDE_URL__ */
export const CLAUDE_URL = typeof __CLAUDE_URL__ !== 'undefined' ? __CLAUDE_URL__ : '';
