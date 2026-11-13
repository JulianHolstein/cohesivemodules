// Extra legend entries for the dependency graph (the plastexdepgraph legend only knows boxes,
// ellipses and colours). Added to blueprint/web/js by plasTeX via `extra-js` in plastex.cfg.
// Edge direction: an arrow A -> B means that B uses A.
$(function () {
  var legend = $("dl.legend");
  if (!legend.length) { return; }
  legend.append(
    "<dt>Dashed arrow</dt><dd>the target uses the source in its <em>statement</em> " +
    "(the source is needed to state it)</dd>" +
    "<dt>Solid arrow</dt><dd>the target uses the source only in its <em>proof</em></dd>"
  );
});
