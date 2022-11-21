const routes = [
  {
    path: "/main",
    name: "MainLayout",
    component: () => import("layouts/MainLayout.vue"),
    children: [
      //GameList Page
      {
        path: "/gamesList",
        component: () => import("pages/GameList.vue"),
        props: true,
      },
      {
        path: "",
        component: () => import("pages/LandingPage.vue"),
      },
      {
        path: "/feed/:id",
        name: "JogoSelecionado",
        component: () => import("pages/GameFeed.vue"),
        props: true,
      },
      {
        path: "/createPost",
        name: "CriarPost",
        component: () => import("pages/CreatePost.vue"),
      },
      {
        path: "/createGroup",
        name: "CriarGrupo",
        component: () => import("pages/CreateGroup.vue"),
      },
      {
        path: "/joinTeam",
        name: "JoinTeam",
        component: () => import("pages/JoinTeam.vue"),
      },
      {
        path: "/profile",
        name: "UserProfile",
        component: () => import("pages/UserProfile.vue"),
      },
      {
        path: "/friendProfile/:id",
        name: "FriendProfile",
        component: () => import("pages/FriendProfile.vue"),
        props: true,
      },
    ],
  },
  {
    path: "/",
    name: "Register",
    component: () => import("src/pages/RegisterPage.vue"),
  },
  {
    path: "/login",
    name: "Login",
    component: () => import("src/pages/LoginPage.vue"),
  },
  {
    path: "/admin",
    name: "Admin",
    component: () => import("src/pages/admin/AdminPage.vue"),
  },

  // Always leave this as last one,
  // but you can also remove it
  {
    path: "/:catchAll(.*)*",
    component: () => import("pages/ErrorNotFound.vue"),
  },
];

export default routes;
