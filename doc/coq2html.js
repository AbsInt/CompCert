function toggleDisplay(id)
{
   var elt = document.getElementById(id);
   if (elt.style.display == 'none') {
     elt.style.display = 'block';
   } else {
     elt.style.display = 'none';
   }
}

function hideAll(cls)
{
  var testClass = new RegExp("(^|s)" + cls + "(s|$)");
  var tag = tag || "*";
  var elements = document.getElementsByTagName("div");
  var current;
  var length = elements.length;
  for(var i=0; i<length; i++){
    current = elements[i];
    if(testClass.test(current.className)) {
      current.style.display = 'none';
    }
  }
}
