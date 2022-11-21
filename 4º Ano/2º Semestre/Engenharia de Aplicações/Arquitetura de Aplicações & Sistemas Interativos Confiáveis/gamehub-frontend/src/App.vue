<template>
  <div class="global">
    <router-view />
  </div>
</template>

<script>
import { defineComponent } from "vue";

export default defineComponent({
  name: "App",
});
</script>

<style>
.global {
  font-family: "Open Sans", sans-serif;
}
</style>
