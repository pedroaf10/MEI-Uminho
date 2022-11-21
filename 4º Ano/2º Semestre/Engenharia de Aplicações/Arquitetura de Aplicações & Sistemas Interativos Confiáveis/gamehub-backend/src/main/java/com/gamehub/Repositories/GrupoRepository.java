package com.gamehub.Repositories;

import com.gamehub.Model.Posts.Grupo;
import org.springframework.data.jpa.repository.Query;
import org.springframework.data.repository.CrudRepository;
import org.springframework.data.repository.query.Param;

public interface GrupoRepository extends CrudRepository<Grupo, Integer> {
    String getNumElementosGrupo = "SELECT count(*) FROM gamer WHERE grupo_id = :grupo_id";

    @Query(value = getNumElementosGrupo, nativeQuery = true)
    int getNumElementosGrupo(@Param("grupo_id") int grupo_id);
}
