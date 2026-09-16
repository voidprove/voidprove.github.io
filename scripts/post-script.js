var coll = document.getElementsByClassName("collapsible");
var i;

for (i = 0; i < coll.length; i++) {
    coll[i].addEventListener("click", function() {
        this.classList.toggle("active");
        var content = this.nextElementSibling;
        if (content.style.maxHeight){
            content.style.maxHeight = null;
        } else {
            content.style.maxHeight = content.scrollHeight + "px";
        } 
    });
}

var navbar = document.getElementsByTagName("nav")[0];
var maindiv= document.getElementsByTagName("main")[0];
var sticky = navbar.offsetTop;
var navbarH= navbar.offsetHeight;
var maindivPadTop = maindiv.style.paddingTop;

window.onscroll = function() {
    if (window.pageYOffset >= sticky) {
        navbar.classList.add("sticky");
        maindiv.style.paddingTop = navbarH + "px";
    } else {
        navbar.classList.remove("sticky");
        maindiv.style.paddingTop = maindivPadTop;
    }
};

var labsMenu = document.getElementById("labs-menu");
if (labsMenu) {
    document.addEventListener("pointerdown", function(event) {
        if (!labsMenu.contains(event.target)) labsMenu.open = false;
    });
    document.addEventListener("keydown", function(event) {
        if (event.key === "Escape" && labsMenu.open) {
            labsMenu.open = false;
            labsMenu.querySelector("summary").focus();
        }
    });
    labsMenu.addEventListener("focusout", function(event) {
        if (!labsMenu.contains(event.relatedTarget)) labsMenu.open = false;
    });
}
