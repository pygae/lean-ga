// https://stackoverflow.com/a/14570614/200764
var observeDOM = (function(){
  var MutationObserver = window.MutationObserver || window.WebKitMutationObserver,
      eventListenerSupported = window.addEventListener;

  return function(obj, callback){
      if( MutationObserver ){
          // define a new observer
          var obs = new MutationObserver(function(mutations, observer){
              if( mutations[0].addedNodes.length || mutations[0].removedNodes.length )
                  callback();
          });
          // have the observer observe foo for changes in children
          obs.observe( obj, { childList:true, subtree:true });
      }
      else if( eventListenerSupported ){
          obj.addEventListener('DOMNodeInserted', callback, false);
          obj.addEventListener('DOMNodeRemoved', callback, false);
      }
  };
})();

// https://stereochro.me/ideas/detecting-broken-images-js
function isImageOk(img) {
  // During the onload event, IE correctly identifies any images that
  // weren't downloaded as not complete. Others should too. Gecko-based
  // browsers act like NS4 in that they report this incorrectly.
  if (!img.complete) {
      return false;
  }

  // However, they do have two very useful properties: naturalWidth and
  // naturalHeight. These give the true size of the image. If it failed
  // to load, either of these should be zero.
  if (typeof img.naturalWidth != "undefined" && img.naturalWidth == 0) {
      return false;
  }

  // No other way of checking: assume it's ok.
  return true;
}

var dependencies = [];


// draw a chart
Reveal.addEventListener('ready', function (event) {
  var all_dates = {
    date: [1973, 1986, 1988, 1989, 1993, 2007],
    name: ["Mizar", "Isabelle", "HOL Family", "Coq", "Metamath", "Agda"]
  };
  var lean_dates = {
    date: [2013, 2015, 2016],
    name: ["Lean", "Lean 2", "Lean 3",],
  };
  var lean_pending_dates = {
    date: [2022],
    name: ["Lean 4"],
  }

  Chart.defaults.global.defaultFontColor='white';
  Chart.defaults.global.defaultColor='white';

  var ctx = document.getElementById('lean-timeline').getContext('2d');
  var chart = new Chart(ctx, {
    // The type of chart we want to create
    type: 'scatter',

    // The data for our dataset
    data: {
        datasets: [{
            pointBackgroundColor: '#42affa',
            pointRadius: 5,
            data: all_dates.date.map(x => { return {x: x, y: 0}; })
        }, {
            pointBackgroundColor: 'green',
            pointRadius: 5,
            data: lean_dates.date.map(x => { return {x: x, y: 0}; })
        }, {
            pointBackgroundColor: 'yellow',
            pointRadius: 5,
            data: lean_pending_dates.date.map(x => { return {x: x, y: 0}; })
        }]
    },

    // // Configuration options go here
    options: {
      maintainAspectRatio: false,
      legend: {
        display: false,
      },
      scales: {
        yAxes: [{
          display: false,
          gridLines: {
            display: false,
          },
          ticks: {min: -1, max: 1},
        }],
        xAxes: [{
          type: 'linear',
          position: 'bottom',
          gridLines: {
            color: "white",
            drawBorder: false,
            major: {
              display: false,
              color: "white",
            },
            ticks: {min: 1965, max: 2025},
            // display: false,
          },
          ticks: {fontColor: "white"}
        }],
      }
    }
  });

});

// head.load('./_assets/js/vendor/fontawesome-all.min.js');
// head.load('./_assets/css/vendor/mermaid.forest.css');
// head.load('./_assets/js/vendor/mermaidAPI.js', function () {
//   mermaidAPI.initialize({
//     startOnLoad: false,
//     cloneCssStyles: true,
//     sequenceDiagram: {
//       height: 30,
//       mirrorActors: false
//     }
//   });
// });

// var fancyboxOptions = {
//   baseClass : 'reveal-fancybox',
//   buttons : [
//     'slideShow',
//     'fullScreen',
//     'thumbs',
//     'download',
//     'zoom',
//     'close'
//   ],
//   smallBtn : false,
//   afterShow: function (instance, slide) {
//     console.info(instance, slide);
//     $(slide.$slide[0]).scrollTop($(slide.$content[0]).offset().top);
//   },
//   afterClose: function (instance, slide) {
//     // console.info( slide.opts.$orig );
//     slide.opts.$orig.each(function (i, a) {
//       console.log(a);
//       $('svg', a).show();
//     });
//     Reveal.layout();
//   }    
// };

// function funcyboxifyImages(cur) {
//   if (!$) {
//     return;
//   }

//   var imgs = $('img', cur || document);
//   imgs.each(function (i, img) {
//     if ($(img).parent().is('[data-fancybox]') || $(img).fancybox == null) {
//       console.log('ignored', img);
//       return;
//     }

//     $(img).wrap('<a href="' + $(img).attr('src') + '" data-fancybox="images"></a>');
//   });
// }

Reveal.addEventListener('ready', function (event) {
  var cur = event.currentSlide;
  decorateSlide(cur, event);
});

Reveal.addEventListener('slidechanged', function (event) {
    var cur = event.currentSlide;    
    decorateSlide(cur, event);
});

function renderIframeSource(cur) {
  var url = cur.getAttribute('data-background-iframe');
  
  var iframeSource = document.querySelector('.iframe-source');
  if (iframeSource == null) {
    iframeSource = document.createElement('div');
    iframeSource.className = 'iframe-source';
    iframeSource.style.display = "none";
    document.body.appendChild(iframeSource);
  }

  if(/^(https?:)?\/\//.test(url)) {
    iframeSource.innerHTML = '<div class="iframe-source">Source: <a target="_blank" href="' + url + '">' 
                              + url + '</a></div>';
    iframeSource.style.display = "block";
  } else {
    iframeSource.innerHTML = "";
    iframeSource.style.display = "none";
  }
}

function decorateSlide(cur, event) {
    console.log(event.indexh, event.indexv);

    renderIframeSource(cur);
    // renderMermaid(cur);

    // Refresh broken image once
    var curImages = cur.querySelectorAll('img');
    for (var i = 0; i < curImages.length; i++) {
      if (!isImageOk(curImages[i])) {
        curImages[i].src = curImages[i].src + '#' + new Date().getTime();
      }
    }

    Reveal.layout();
}

// function renderMermaid(cur) {
//   var diagramCodeTag = cur.querySelector('code.lang-mermaid');
//   var renderedDiagram = cur.querySelector('.mermaidSvg');

//   if(diagramCodeTag != null && mermaidAPI != null) {
//     // console.log(diagramCodeTag);
//     var diagramSource = diagramCodeTag.textContent;
//     // console.log(diagramSource);

//     var id = Math.floor(Math.random() * 1000).toString();
//     var fullId = 'mermaid-diagram-' + id;

//     mermaidAPI.render(fullId, diagramSource, function (svgCode, bindFunctions) {
//       // console.log(svgCode);
    
//       var svgDiv = document.createElement('a');
//       svgDiv.className = 'mermaidSvg';
//       svgDiv.setAttribute('data-fancybox', 'images');
//       svgDiv.setAttribute('data-src', '#' + fullId);

//       svgDiv.innerHTML = svgCode;

//       cur.insertBefore(svgDiv, diagramCodeTag.parentNode);

//       diagramCodeTag.style.display = "none";

//       if(renderedDiagram != null) {
//         renderedDiagram.remove();
//       }

//       return;
//     });
//   }
// }

if (window.location.search.match( /print-pdf/gi )) {
  Reveal.addEventListener('ready', function () {
    var slides = document.querySelectorAll('.reveal .slides section');
    slides.forEach(function (cur) {
      // renderMermaid(cur);

      var codeComments = cur.querySelectorAll('.fragment[data-code-focus]');

      if (codeComments) {
        var codeFocus = cur.querySelectorAll('code.focus');
        codeFocus.forEach(function (c) {
            c.style.zoom = 0.5;
        });
      }
      
      codeComments.forEach(function (codeComment) {
        var codeLineSpec = codeComment.getAttribute('data-code-focus');
        codeComment.classList.remove('fragment');
        codeComment.style.zoom = 1 / (codeComments.length || 2) * 2;
        var codeLineSpecSpan = document.createElement('span');
        codeLineSpecSpan.textContent = 'line ' + codeLineSpec + ': ';
        codeLineSpecSpan.style.cssFloat = 'left';
        codeLineSpecSpan.style.marginLeft = '10%';
        codeComment.insertBefore(codeLineSpecSpan, codeComment.firstChild);
      });

      if (cur.hasAttribute('data-background-iframe')) {
        // console.log(cur);

        var iframeSource = document.createElement('div');
        iframeSource.className = 'iframe-source';

        var url = cur.getAttribute('data-background-iframe');

        var maxLen = 100;

        iframeSource.innerHTML = 'Source: <a target="_blank" href="' + url + '">' 
                              + ( url.length > maxLen ? (url.substr(0, maxLen) + '...') : url) + '</a>';
        iframeSource.style.display = "block";
        cur.appendChild(iframeSource);
      }
      
    });
  });
}

// var revealConfig = Reveal.getConfig();

// revealConfig.dependencies = (revealConfig.dependencies || []).concat(dependencies);

// // console.log('Reveal.getConfig():', revealConfig);

// revealConfig.markdown = revealConfig.markdown || {};

// Object.defineProperty(revealConfig.markdown, "renderer", { get: function () {
//     var customRenderer = new marked.Renderer();

//     function escape(html, encode) {
//       return html
//         .replace(!encode ? /&(?!#?\w+;)/g : /&/g, '&amp;')
//         .replace(/</g, '&lt;')
//         .replace(/>/g, '&gt;')
//         .replace(/"/g, '&quot;')
//         .replace(/'/g, '&#39;');
//     }

//     var origCode = customRenderer.code.bind(customRenderer);
//     customRenderer.code = function (code, lang, escaped) {
//       if (lang != 'xxx') {
//         return origCode(code, lang, escaped);
//       } else {
//         return '<pre>xxx: TODO</pre>';
//       }
//     }

//     return customRenderer;
//   },
//   set: function (v) {
//     this._renderer = v;
//   },
//   enumerable: true
// });